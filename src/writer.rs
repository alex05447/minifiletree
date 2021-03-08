use {
    crate::{
        error::*, util::*, FileTreeHeader, InternedString, PathHash, PathPart, PathPartIndex,
        StringIndex,
    },
    std::{
        collections::HashMap,
        hash::{BuildHasher, Hasher},
        io::{self, Write},
        iter::Iterator,
        mem::size_of,
        num::NonZeroU32,
        path::{Component, Path, PathBuf},
    },
};

type StringLookup = MultiMap<PathHash, StringIndex>;
type SubpathLookup = MultiMap<PathHash, PathPartIndex>;

/// Provides an API to append hashed file paths to a buffer and store them space-efficiently.
/// Deduplicates unique path part / component strings and file tree nodes.
/// When finished, writes the data to a binary blob which may then be saved, read by a [`reader`] and used to lookup the full file paths by their hashes.
///
/// Uses a user-provided [`hasher builder`] to hash the path parts / components.
///
/// [`reader`]: struct.FileTreeReader.html
/// [`hasher builder`]: std::hash::BuildHasher
pub struct FileTreeWriter<H: BuildHasher> {
    hash_builder: H,

    /// Temporary lookup map from each valid subpath added so far to its entry in the `path_parts` lookup array.
    /// Needed only by the writer, not serialized to the data blob.
    subpath_lookup: SubpathLookup,

    /// Temporary lookup map from a single path part string's hash to its index
    /// (indices if there's hash string hash collisions) in the `string_table`.
    /// Needed only by the writer, not serialized to the data blob.
    string_lookup: StringLookup,

    /// Temporary string buffer used by the writer to normalize the paths.
    lowercase_buffer: String,

    /// Persistent lookup map from a hash of each valid leaf file path to its entry in the `path_parts` lookup array.
    /// Needed by the writer and serialized to the data blob.
    path_lookup: HashMap<PathHash, PathPartIndex>,

    /// Persistent array of valid path parts / components added so far.
    /// Indexed into by entries of `subpath_lookup` and `path_lookup`.
    /// Needed by the writer and serialized to the data blob.
    path_parts: Vec<PathPart>,

    /// Persistent array of unique string offsets and lengths in the `strings` buffer.
    /// Needed by the writer and serialized to the data blob.
    string_table: Vec<InternedString>,

    /// Persistent string storage buffer.
    /// All unique strings are stored in it contiguously.
    /// Indexed into by entries in the `offsets_and_lengths` array.
    /// Needed by the writer and serialized to the data blob.
    strings: String,
}

impl<H: BuildHasher> FileTreeWriter<H> {
    /// Create a new [`file tree writer`] with the provided `hash_builder`.
    ///
    /// `hash_builder` is used to hash [`inserted`] paths and their subpaths / individual components.
    ///
    /// [`file tree writer`]: struct.FileTreeWriter.html
    /// [`inserted`]: #method.insert
    pub fn new(hash_builder: H) -> Self {
        Self {
            hash_builder,
            subpath_lookup: SubpathLookup::new(),
            string_lookup: StringLookup::new(),
            lowercase_buffer: String::new(),
            path_lookup: HashMap::new(),
            path_parts: Vec::new(),
            string_table: Vec::new(),
            strings: String::new(),
        }
    }

    /// Inserts the `path` to a file into the writer and returns its [`hash`].
    ///
    /// Returned [`hash`] is calculated by hashing each path component converted to lowercase in order, root to leaf. Separators are not included.
    ///
    /// Valid paths are relative, do no contain prefixes, root/curent/parent directory redirectors,
    /// and contain valid UTF-8.
    /// Paths are converted to lower case before hashing / inserting.
    /// Path hash collisions are treated as [`errors`].
    ///
    /// Examples of valid paths: "foo/bar/baz.txt", "BOB" (inserted as "bob"), "áéíóú\\αβγδε".
    /// Examples of invalid paths: "C:/foo" (has a prefix and a root directory),
    /// "/bar/baz.txt" (has a root directory), "a/../b" (has a parent directory),
    /// "f/oo" and "fo/o" (these have the same hash).
    ///
    /// [`hash`]: type.PathHash.html
    /// [`errors`]: enum.FileTreeWriterError.html#variant.PathHashCollision
    pub fn insert<P: AsRef<Path>>(&mut self, path: P) -> Result<PathHash, FileTreeWriterError> {
        use FileTreeWriterError::*;

        let path = path.as_ref();

        // Validate the path, count the number of parts/components, and hash it to determine if we have a path hash collision.
        // Need to preprocess to avoid inserting strings / subpaths into the lookup if the path is ultimately found to be invalid.
        let mut num_parts = 0;
        let mut hasher = self.hash_builder.build_hasher();

        for (idx, path_part) in path.components().enumerate() {
            match path_part {
                Component::Normal(path_part) => {
                    if path_part.is_empty() {
                        return Err(EmptyPathComponent(
                            path.components().take(idx).collect::<PathBuf>(),
                        ));
                    }

                    if let Some(path_part) = path_part.to_str() {
                        // Convert to lowercase, then hash.
                        hasher.write(
                            Self::to_lower_str(path_part, &mut self.lowercase_buffer).as_bytes(),
                        );
                    } else {
                        return Err(InvalidUTF8(
                            path.components().take(idx).collect::<PathBuf>(),
                        ));
                    }

                    num_parts += 1;
                }
                Component::Prefix(_) => return Err(PrefixedPath),
                Component::CurDir | Component::ParentDir | Component::RootDir => {
                    return Err(InvalidPathComponent(
                        path.components().take(idx).collect::<PathBuf>(),
                    ))
                }
            }
        }

        if num_parts == 0 {
            return Err(EmptyPath);
        }

        // Check for full file path hash collisions.
        let path_hash = hasher.finish();

        if let Some(&existing_index) = self.path_lookup.get(&path_hash) {
            return Err(FileTreeWriterError::PathHashCollision(
                self.path_string(existing_index).into(),
            ));
        }

        hasher = self.hash_builder.build_hasher();

        // Index of the parent path part/component for each processed path part/component;
        // index of the leaf/file path part/component after the last one was processed.
        let mut parent_index = None;

        for (idx, path_part) in path.components().enumerate() {
            // If it's the last path part/node, it must be the name of a file
            // (and thus no other file/folder is allowed to exist at that path).
            let last = idx == (num_parts - 1);

            match path_part {
                Component::Normal(path_part) => {
                    // Must succeed - validated above.
                    if let Some(path_part) = path_part.to_str() {
                        debug_assert!(!path_part.is_empty());

                        // Convert to lowercase.
                        let path_part = Self::to_lower_str(path_part, &mut self.lowercase_buffer);

                        // Then hash.
                        hasher.write(path_part.as_bytes());
                        let subpath_hash = hasher.finish();

                        // Check if the path part for this subpath already exists.
                        let mut path_part_index: Option<PathPartIndex> = None;

                        if let Some(existing_index) = Self::find_existing_subpath(
                            &self.subpath_lookup,
                            &self.path_parts,
                            &self.string_table,
                            &self.strings,
                            path_part,
                            subpath_hash,
                            parent_index,
                        ) {
                            // Make sure that
                            // 1) we're not processing the leaf/file part/component
                            // (because we can't have a new file with the same name as an existing file/folder);
                            // 2) the subpath is not a path to an existing file
                            // (because we can't have a new file/folder with the same name as an existing file);
                            if last {
                                return Err(FileOrFolderAlreadyExistsAtFilePath(
                                    self.path_string(existing_index).into(),
                                ));
                            }

                            if self.path_lookup.contains_key(&subpath_hash) {
                                return Err(FileAlreadyExistsAtFileOrFolderPath(
                                    self.path_string(existing_index).into(),
                                ));
                            }

                            path_part_index.replace(existing_index);
                        }

                        let string_lookup = &mut self.string_lookup;
                        let string_table = &mut self.string_table;
                        let strings = &mut self.strings;
                        let path_parts = &mut self.path_parts;
                        let hash_builder = &self.hash_builder;
                        let subpath_lookup = &mut self.subpath_lookup;

                        let path_part_index = path_part_index.unwrap_or_else(|| {
                            // If this subpath doesn't exist yet, we're going to add it.
                            let path_part_index = Self::add_path_part(
                                string_lookup,
                                string_table,
                                strings,
                                path_parts,
                                hash_builder,
                                path_part,
                                parent_index,
                            );

                            subpath_lookup.insert(subpath_hash, path_part_index);

                            path_part_index
                        });

                        // Update the parent index to the current path part index.
                        parent_index.replace(path_part_index);

                    // Unreachable - validated above.
                    } else {
                        debug_unreachable();
                    }
                }
                // Unreachable - validated above.
                _ => debug_unreachable(),
            }
        }

        self.lowercase_buffer.clear();

        // Update the path lookup with the path part index for the lead node.
        debug_assert_eq!(path_hash, hasher.finish());

        // Must succeed if we got here, or we'd error out above.
        debug_assert!(parent_index.is_some());
        let parent_index = parent_index.unwrap_or(0);

        let _none = self.path_lookup.insert(path_hash, parent_index);
        // Must be none, or we'd error out above.
        debug_assert!(_none.is_none());

        Ok(path_hash)
    }

    /// Consumes the [`file tree writer`] and serializes its data to the writer `w`.
    /// Produced data blob may then be used by the [`FileTreeReader`].
    ///
    /// [`file tree writer`]: struct.FileTreeWriter.html
    /// [`FileTreeReader`]: struct.FileTreeReader.html
    pub fn write<W: Write>(self, w: &mut W) -> Result<usize, io::Error> {
        let mut written = 0;

        // Header.
        written += FileTreeHeader::write(
            w,
            self.path_lookup.len() as _,
            self.path_parts.len() as _,
            self.string_table.len() as _,
        )?;

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Path lookup.

        // Get and sort the path hashes.
        // TODO: use a `BTreeMap`?
        let mut path_hashes = self.path_lookup.keys().cloned().collect::<Vec<_>>();
        path_hashes.sort();

        // Write the path hashes.
        for &path_hash in path_hashes.iter() {
            written += w.write(&u64_to_bin_bytes(path_hash))?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Write the path part indices.
        for path_part_index in path_hashes
            .iter()
            .map(|path_hash| *self.path_lookup.get(path_hash).unwrap())
        {
            written += w.write(&u32_to_bin_bytes(path_part_index))?;
        }

        // Align to 8 bytes.
        let alignment = written % 8;

        for _ in 0..alignment {
            written += w.write(&[0u8])?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Path parts array.

        for &path_part in self.path_parts.iter() {
            written += w.write(&u32_to_bin_bytes(path_part.string_index))?;
            written += w.write(&u32_to_bin_bytes(
                path_part.parent_index.map(NonZeroU32::get).unwrap_or(0),
            ))?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // String table.

        // Patch up the string offsets to be relative to the start of the blob.
        let string_offset =
            (written + self.string_table.len() * size_of::<InternedString>()) as u32;

        for &offset_and_length in self.string_table.iter() {
            written += w.write(&u32_to_bin_bytes(string_offset + offset_and_length.offset))?;
            written += w.write(&u32_to_bin_bytes(offset_and_length.len))?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Strings.

        written += w.write(self.strings.as_bytes())?;

        Ok(written as _)
    }

    /// Returns the index of the existing path part with `subpath_hash` and the current component `path_part`, if one exists.
    /// The caller guarantees `parent_index` is valid, if `Some`.
    fn find_existing_subpath(
        subpath_lookup: &SubpathLookup,
        path_parts: &Vec<PathPart>,
        string_table: &Vec<InternedString>,
        strings: &String,
        path_part: &str,
        subpath_hash: PathHash,
        parent_index: Option<PathPartIndex>,
    ) -> Option<PathPartIndex> {
        let mut result = None;

        if let Some(existing_indices) = subpath_lookup.get(&subpath_hash) {
            'indices: for &existing_index in existing_indices {
                let mut existing_subpath =
                    Self::iter_impl(path_parts, string_table, strings, existing_index);

                // Must be `Some` - empty paths are not allowed.
                if let Some(existing_path_part) = existing_subpath.next() {
                    if path_part != existing_path_part {
                        // New and existing path part strings mismatch.
                        debug_assert!(result.is_none());
                        continue 'indices;
                    }
                } else {
                    debug_unreachable();
                }

                if let Some(mut new_subpath) = parent_index.map(|parent_index| {
                    Self::iter_impl(path_parts, string_table, strings, parent_index)
                }) {
                    loop {
                        if let Some(existing_path_part) = existing_subpath.next() {
                            if let Some(new_path_part) = new_subpath.next() {
                                if new_path_part != existing_path_part {
                                    // New and existing path part strings mismatch.
                                    debug_assert!(result.is_none());
                                    continue 'indices;
                                }
                            } else {
                                // New path is shorter then the existing one.
                                debug_assert!(result.is_none());
                                continue 'indices;
                            }
                        } else if new_subpath.next().is_some() {
                            // Existing path is shorter then the new one.
                            debug_assert!(result.is_none());
                            continue 'indices;
                        } else {
                            // New and existing paths are the same length.
                            break;
                        }
                    }

                    result.replace(existing_index);
                    break 'indices;
                } else if existing_subpath.next().is_none() {
                    // New and existing paths are the same length - 1.
                    result.replace(existing_index);
                    break 'indices;
                } else {
                    // New path is shorter then the existing one.
                    debug_assert!(result.is_none());
                }
            }
        }

        result
    }

    fn to_lower_str<'s>(string: &str, buf: &'s mut String) -> &'s str {
        buf.clear();
        to_lower_str(string, buf);
        buf.as_str()
    }

    fn hash_string(mut hasher: H::Hasher, string: &str) -> PathHash {
        hasher.write(string.as_bytes());
        hasher.finish()
    }

    /// Adds the unique `string` with `hash` to the lookup data structures and returns its index.
    /// The caller guarantees `string` with `hash` has not been interned yet.
    fn intern_string(
        string_lookup: &mut StringLookup,
        string_table: &mut Vec<InternedString>,
        strings: &mut String,
        string: &str,
        hash: PathHash,
    ) -> StringIndex {
        debug_assert!(!string.is_empty());

        let offset_and_len = InternedString {
            offset: strings.len() as _,
            len: string.len() as _,
        };
        strings.push_str(string);
        let string_index = string_table.len() as _;
        string_table.push(offset_and_len);
        string_lookup.insert(hash, string_index);
        string_index
    }

    /// Returns the string index of the interned `string`, if it is interned, or interns it and returns its index.
    fn interned_string_index(
        string_lookup: &mut StringLookup,
        string_table: &mut Vec<InternedString>,
        strings: &mut String,
        hasher: H::Hasher,
        string: &str,
    ) -> StringIndex {
        debug_assert!(!string.is_empty());

        // First hash the path part's string and check if was already added.
        let string_hash = Self::hash_string(hasher, string);

        if let Some(string_index) = string_lookup
            // First lookup by string hash.
            .get(&string_hash)
            // Then compare the strings.
            .map(|string_indices| {
                string_indices.iter().cloned().find(|&string_index| {
                    string_impl(string_table, strings, string_index) == string
                })
            })
            .flatten()
        {
            // The `string` already exists - return its index.
            string_index
        } else {
            // Else the string does not exist - intern it and return its index.
            Self::intern_string(string_lookup, string_table, strings, string, string_hash)
        }
    }

    fn add_path_part(
        string_lookup: &mut StringLookup,
        string_table: &mut Vec<InternedString>,
        strings: &mut String,
        path_parts: &mut Vec<PathPart>,
        hash_builder: &H,
        path_part: &str,
        parent_index: Option<PathPartIndex>,
    ) -> PathPartIndex {
        let string_index = Self::interned_string_index(
            string_lookup,
            string_table,
            strings,
            hash_builder.build_hasher(),
            path_part,
        );

        // Add a new path part to the lookup array, using the current parent index, if any (don't forget to `+1`).
        let path_part_index = path_parts.len() as PathPartIndex;

        let path_part = PathPart {
            parent_index: parent_index
                .map(|parent_index| unsafe { NonZeroU32::new_unchecked(parent_index + 1) }),
            string_index,
        };
        debug_assert!(!path_parts.contains(&path_part));
        path_parts.push(path_part);

        path_part_index
    }

    /// Returns a reverse (leaf to root) iterator over path parts / components of the path starting with the part at `index`.
    /// The caller guarantees the path part `index` is valid.
    fn iter(&self, index: PathPartIndex) -> impl Iterator<Item = &'_ str> {
        Self::iter_impl(&self.path_parts, &self.string_table, &self.strings, index)
    }

    /// Returns a reverse (leaf to root) iterator over path parts / components of the path starting with the part at `index`.
    /// The caller guarantees the path part `index` is valid.
    fn iter_impl<'a>(
        path_parts: &'a Vec<PathPart>,
        string_table: &'a Vec<InternedString>,
        strings: &'a String,
        index: PathPartIndex,
    ) -> impl Iterator<Item = &'a str> {
        debug_assert!((index as usize) < path_parts.len());

        PathIter::new(
            path_parts,
            string_table,
            strings,
            Some(unsafe { *path_parts.get_unchecked(index as usize) }),
        )
    }

    /// The caller guarantees the path part `index` is valid.
    fn build_path_string(&self, index: PathPartIndex, string: &mut String) {
        build_path_string(|| self.iter(index), string);
    }

    /// The caller guarantees the path part `index` is valid.
    fn path_string(&self, index: PathPartIndex) -> String {
        let mut string = String::new();
        self.build_path_string(index, &mut string);
        string
    }

    #[cfg(test)]
    fn lookup(&self, hash: PathHash) -> Option<String> {
        self.path_lookup
            .get(&hash)
            .map(|&path_part_index| self.path_string(path_part_index))
    }
}

/// The caller guarantees the path part `index` is valid.
fn path_part_impl(path_parts: &Vec<PathPart>, index: PathPartIndex) -> PathPart {
    debug_assert!((index as usize) < path_parts.len());
    unsafe { *path_parts.get_unchecked(index as usize) }
}

/// The caller guarantees the string `index` is valid.
fn string_impl<'s>(
    string_table: &Vec<InternedString>,
    strings: &'s String,
    index: StringIndex,
) -> &'s str {
    debug_assert!((index as usize) < string_table.len());
    let string = unsafe { string_table.get_unchecked(index as usize) };
    debug_assert!((string.offset as usize) < strings.len());
    debug_assert!(((string.offset + string.len) as usize) <= strings.len());
    unsafe { strings.get_unchecked(string.offset as usize..(string.offset + string.len) as usize) }
}

struct PathIter<'a> {
    path_parts: &'a Vec<PathPart>,
    string_table: &'a Vec<InternedString>,
    strings: &'a String,
    cur_part: Option<PathPart>,
}

impl<'a> PathIter<'a> {
    fn new(
        path_parts: &'a Vec<PathPart>,
        string_table: &'a Vec<InternedString>,
        strings: &'a String,
        cur_part: Option<PathPart>,
    ) -> Self {
        Self {
            path_parts,
            string_table,
            strings,
            cur_part,
        }
    }
}

impl<'a> Iterator for PathIter<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(path_part) = self.cur_part.take() {
            let str = string_impl(self.string_table, self.strings, path_part.string_index);

            if let Some(parent_index) = path_part.parent_index {
                self.cur_part
                    .replace(path_part_impl(self.path_parts, parent_index.get() - 1));
            }

            Some(str)
        } else {
            None
        }
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use {super::*, seahash::SeaHasher};

    #[derive(Default)]
    struct BuildSeaHasher;

    impl BuildHasher for BuildSeaHasher {
        type Hasher = SeaHasher;

        fn build_hasher(&self) -> Self::Hasher {
            SeaHasher::new()
        }
    }

    #[test]
    fn EmptyPath() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

        assert!(matches!(
            writer.insert("").err().unwrap(),
            FileTreeWriterError::EmptyPath
        ));
    }

    #[cfg(windows)]
    #[test]
    fn InvalidUTF8() {
        use std::os::windows::ffi::OsStringExt;

        let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

        let bytes: &[u16] = &[0xD800];

        let os_string = std::ffi::OsString::from_wide(bytes);

        assert!(
            matches!(writer.insert(&os_string).err().unwrap(), FileTreeWriterError::InvalidUTF8(x) if x == PathBuf::new())
        );
    }

    #[test]
    fn PrefixedPath() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

        assert!(matches!(
            writer.insert("C:/foo").err().unwrap(),
            FileTreeWriterError::PrefixedPath
        ));
    }

    #[test]
    fn InvalidPathComponent() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

        assert!(
            matches!(writer.insert("/foo").err().unwrap(), FileTreeWriterError::InvalidPathComponent(x) if x == PathBuf::new())
        );
        assert!(
            matches!(writer.insert("./foo").err().unwrap(), FileTreeWriterError::InvalidPathComponent(x) if x == PathBuf::new())
        );
        assert!(
            matches!(writer.insert("foo/../bar").err().unwrap(), FileTreeWriterError::InvalidPathComponent(x) if x == PathBuf::from("foo"))
        );
    }

    #[test]
    fn FileOrFolderAlreadyExistsAtFilePath() {
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

            let foo_bar = writer.insert("foo/bar").unwrap();

            assert_eq!(writer.lookup(foo_bar).unwrap(), "foo/bar".to_string());

            assert!(
                matches!(writer.insert("foo").err().unwrap(), FileTreeWriterError::FileOrFolderAlreadyExistsAtFilePath(x) if x == PathBuf::from("foo"))
            );
        }

        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

            let foo_bar_baz = writer.insert("foo/bar/baz").unwrap();

            assert_eq!(
                writer.lookup(foo_bar_baz).unwrap(),
                "foo/bar/baz".to_string()
            );

            assert!(
                matches!(writer.insert("foo/bar").err().unwrap(), FileTreeWriterError::FileOrFolderAlreadyExistsAtFilePath(x) if x == PathBuf::from("foo/bar"))
            );
        }
    }

    #[test]
    fn FileAlreadyExistsAtFileOrFolderPath() {
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

            let foo = writer.insert("foo").unwrap();

            assert_eq!(writer.lookup(foo).unwrap(), "foo".to_string());

            assert!(
                matches!(writer.insert("foo/bar").err().unwrap(), FileTreeWriterError::FileAlreadyExistsAtFileOrFolderPath(x) if x == PathBuf::from("foo"))
            );
        }

        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

            let foo_bar = writer.insert("foo/bar").unwrap();

            assert_eq!(writer.lookup(foo_bar).unwrap(), "foo/bar".to_string());

            assert!(
                matches!(writer.insert("foo/bar/baz").err().unwrap(), FileTreeWriterError::FileAlreadyExistsAtFileOrFolderPath(x) if x == PathBuf::from("foo/bar"))
            );
        }
    }

    struct FNV1aHasher(u32);

    impl FNV1aHasher {
        fn new() -> Self {
            const FNV1A_SEED: u32 = 0x811C_9DC5;
            Self(FNV1A_SEED)
        }
    }

    impl Hasher for FNV1aHasher {
        fn write(&mut self, bytes: &[u8]) {
            const FNV1A_PRIME: u32 = 0x0100_0193;

            for byte in bytes {
                self.0 = (self.0 ^ *byte as u32).wrapping_mul(FNV1A_PRIME);
            }
        }

        fn finish(&self) -> u64 {
            self.0 as u64
        }
    }

    struct BuildFNV1aHasher;

    impl BuildHasher for BuildFNV1aHasher {
        type Hasher = FNV1aHasher;

        fn build_hasher(&self) -> Self::Hasher {
            Self::Hasher::new()
        }
    }

    #[test]
    fn fnv1a_hash_collisions() {
        fn string_hash_fnv1a(string: &str) -> u64 {
            let mut hasher = FNV1aHasher::new();
            hasher.write(string.as_bytes());
            hasher.finish()
        }

        // https://softwareengineering.stackexchange.com/questions/49550/which-hashing-algorithm-is-best-for-uniqueness-and-speed

        assert_eq!(string_hash_fnv1a("costarring"), string_hash_fnv1a("liquid"),);

        assert_eq!(
            string_hash_fnv1a("declinate"),
            string_hash_fnv1a("macallums"),
        );

        assert_eq!(string_hash_fnv1a("altarage"), string_hash_fnv1a("zinke"),);

        assert_eq!(string_hash_fnv1a("altarages"), string_hash_fnv1a("zinkes"),);

        assert_ne!(string_hash_fnv1a("foo"), string_hash_fnv1a("bar"),);
    }

    #[test]
    fn PathHashCollision() {
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

            let fo_o = writer.insert("fo/o").unwrap();

            assert_eq!(writer.lookup(fo_o).unwrap(), "fo/o".to_string());

            assert!(
                matches!(writer.insert("f/oo").err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x == PathBuf::from("fo/o"))
            );
        }

        {
            let mut writer = FileTreeWriter::new(BuildFNV1aHasher);

            let cost_arring = writer.insert("cost/arring").unwrap();

            assert_eq!(
                writer.lookup(cost_arring).unwrap(),
                "cost/arring".to_string()
            );

            assert!(
                matches!(writer.insert("liq/uid").err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x == PathBuf::from("cost/arring"))
            );
        }

        {
            let mut writer = FileTreeWriter::new(BuildFNV1aHasher);

            let altarag_es = writer.insert("altarag/es").unwrap();

            assert_eq!(writer.lookup(altarag_es).unwrap(), "altarag/es".to_string());

            assert!(
                matches!(writer.insert("zink/es").err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x == PathBuf::from("altarag/es"))
            );
        }

        {
            // But this should work.

            // "foo/bar/baz"
            //   1 / 2 / 3
            // "bar"
            //   2 <- hash collision, shorter new path
            // "bob/foo/bar"
            //   4   1   2 <- hash collision, longer new path
            //       ^- hash collision, longer new path
            // "foo/bill"
            //   1   2 <- hash collision, string mismatch

            struct MockHasher(u64);

            impl Hasher for MockHasher {
                fn write(&mut self, bytes: &[u8]) {
                    self.0 = match std::str::from_utf8(bytes).unwrap() {
                        "foo" => 1,
                        "bar" => 2,
                        "baz" => 3,
                        "bob" => 4,
                        "bill" => 2,
                        _ => unreachable!(),
                    }
                }

                fn finish(&self) -> u64 {
                    self.0
                }
            }

            struct BuildMockHasher;

            impl BuildHasher for BuildMockHasher {
                type Hasher = MockHasher;

                fn build_hasher(&self) -> Self::Hasher {
                    MockHasher(0)
                }
            }

            {
                let mut writer = FileTreeWriter::new(BuildMockHasher);

                let foo_bar_baz = writer.insert("foo/bar/baz").unwrap();
                assert_eq!(foo_bar_baz, 3);
                assert_eq!(
                    writer.lookup(foo_bar_baz).unwrap(),
                    "foo/bar/baz".to_string()
                );

                let bar = writer.insert("bar").unwrap();
                assert_eq!(bar, 2);
                assert_eq!(writer.lookup(bar).unwrap(), "bar".to_string());
            }

            {
                let mut writer = FileTreeWriter::new(BuildMockHasher);

                let foo_bar_baz = writer.insert("foo/bar/baz").unwrap();
                assert_eq!(foo_bar_baz, 3);
                assert_eq!(
                    writer.lookup(foo_bar_baz).unwrap(),
                    "foo/bar/baz".to_string()
                );

                let bob_foo_bar = writer.insert("bob/foo/bar").unwrap();
                assert_eq!(bob_foo_bar, 2);
                assert_eq!(
                    writer.lookup(bob_foo_bar).unwrap(),
                    "bob/foo/bar".to_string()
                );
            }

            {
                let mut writer = FileTreeWriter::new(BuildMockHasher);

                let foo_bar_baz = writer.insert("foo/bar/baz").unwrap();
                assert_eq!(foo_bar_baz, 3);
                assert_eq!(
                    writer.lookup(foo_bar_baz).unwrap(),
                    "foo/bar/baz".to_string()
                );

                let foo_bill = writer.insert("foo/bill").unwrap();
                assert_eq!(foo_bill, 2);
                assert_eq!(writer.lookup(foo_bill).unwrap(), "foo/bill".to_string());
            }
        }
    }
}

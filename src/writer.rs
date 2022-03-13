use {
    crate::*,
    minifilepath::{FilePath, FilePathBuf, FilePathComponent},
    ministr::NonEmptyStr,
    std::{
        collections::HashMap,
        hash::{BuildHasher, Hasher},
        io::{self, Write},
        iter::{ExactSizeIterator, Iterator},
        mem::size_of,
    },
};

/// Here the `PathHash` key is the accumulated hash of the entire subpath so far.
type SubpathLookup = MultiMap<PathHash, PathComponentIndex>;
/// Here the `PathHash` key is the hash of just a single path component.
type StringLookup = MultiMap<PathHash, StringIndex>;

#[derive(Clone, Copy)]
struct PathComponentAndMetadata {
    path_component: PathComponent,
    /// See `LeafPathComponent::num_components`.
    num_components: NumComponents,
    /// See `LeafPathComponent::string_len` (but for the path starting at the `path_component`).
    string_len: FullStringLength,
}

/// Provides an API to append [`hashed`](PathHash) [`file paths`](FilePath) to a buffer and store them space-efficiently.
/// Deduplicates unique [`path component`](FilePathComponent) strings and file tree nodes.
///
/// When finished, [`writes`](FileTreeWriter::write) the data to a binary blob which may then be saved, read by a [`FileTreeReader`]
/// and used to lookup the full file paths by their hashes.
///
/// Uses a user-provided [`hasher builder`](std::hash::BuildHasher) to hash the path components.
pub struct FileTreeWriter<H: BuildHasher> {
    /// User-provided hasher builder used to build the hasher which is used to hash the paths.
    hash_builder: H,

    /// Temporary lookup map from each valid subpath added so far to its index
    /// (or indices, if there's subpath string hash collisions) in the path_components lookup array.
    ///
    /// Needed only by the writer, not serialized to the data blob.
    subpath_lookup: SubpathLookup,

    /// Temporary lookup map from a single path component string's hash to its index
    /// (or indices, if there's subpath string hash collisions) in the `string_table`.
    ///
    /// Needed only by the writer, not serialized to the data blob.
    string_lookup: StringLookup,

    /// Persistent lookup map from a full file path hash to its leaf path component.
    /// `HashMap` and not a `MultiMap` because we don't allow hash collisions for leaf file paths.
    ///
    /// Needed by the writer and serialized to the data blob.
    path_lookup: HashMap<PathHash, LeafPathComponent>,

    /// Persistent array of valid path components added so far (and some metadata useful when building the path string slightly more efficiently).
    /// Indexed into by entries of `subpath_lookup` and `path_lookup`.
    ///
    /// Needed by the writer and serialized to the data blob (path components only, not the metadata).
    path_components: Vec<PathComponentAndMetadata>,

    /// Persistent array of unique string offsets and lengths in the `strings` buffer.
    ///
    /// Needed by the writer and serialized to the data blob.
    string_table: Vec<InternedString>,

    /// Persistent string storage buffer.
    /// All unique strings are stored in it contiguously.
    /// Indexed into by entries in the `string_table` array.
    ///
    /// Needed by the writer and serialized to the data blob.
    strings: String,
}

impl<H: BuildHasher> FileTreeWriter<H> {
    /// Create a new [`file tree writer`] with the provided [`hash_builder`].
    ///
    /// [`hash_builder`] is used to hash [`inserted`] paths and their subpaths / individual components.
    ///
    /// [`file tree writer`]: struct.FileTreeWriter.html
    /// [`inserted`]: #method.insert
    /// [`hash_builder`]: std::hash::BuildHasher
    pub fn new(hash_builder: H) -> Self {
        Self {
            hash_builder,
            subpath_lookup: SubpathLookup::new(),
            string_lookup: StringLookup::new(),
            path_lookup: HashMap::new(),
            path_components: Vec::new(),
            string_table: Vec::new(),
            strings: String::new(),
        }
    }

    /// Inserts the [`path`](FilePath) to a file into the writer and returns its [`hash`].
    ///
    /// Returned [`hash`] is calculated by hashing each path component, root to leaf (excluding the separators),
    /// using the [`hash builder`](std::hash::BuildHasher) provided in the call to [`new`](#methods.new).
    ///
    /// Full path hash collisions are treated as [`errors`].
    ///
    /// [`hash`]: type.PathHash.html
    /// [`errors`]: enum.FileTreeWriterError.html#variant.PathHashCollision
    pub fn insert<P: AsRef<FilePath>>(&mut self, path: P) -> Result<PathHash, FileTreeWriterError> {
        use FileTreeWriterError::*;

        let path = path.as_ref();

        // Count the number of components, and hash the path fully to determine if we have a path hash collision.
        // Need to preprocess to avoid inserting strings / subpaths into the lookup if the path is ultimately found to be invalid.
        let (num_components, path_hash) = {
            let mut hasher = self.hash_builder.build_hasher();
            let mut num_components: NumComponents = 0;

            for path_component in path.components() {
                hasher.write(path_component.as_bytes());
                num_components += 1;
            }

            debug_assert!(num_components > 0, "valid paths are not empty");

            (num_components, hasher.finish())
        };

        // Check for full file path hash collisions.
        if let Some(&existing_path_component) = self.path_lookup.get(&path_hash) {
            return Err(FileTreeWriterError::PathHashCollision(
                self.path_buf(existing_path_component.path_component_index),
            ));
        }

        let mut hasher = self.hash_builder.build_hasher();

        // Index of the parent path component for each processed path component in the loop below;
        // index of the leaf/file path component after the last one was processed.
        let mut parent_index = None;
        let mut string_len: FullStringLength = 0;

        for (path_component_idx, path_component) in path.components().enumerate() {
            // If it's the last path component, it must be the name of a file
            // (and thus no other file/folder is allowed to exist at that path).
            let last = path_component_idx == (num_components - 1) as _;

            string_len += path_component.len() as FullStringLength;

            // Hash the subpath so far.
            hasher.write(path_component.as_bytes());
            let subpath_hash = hasher.finish();

            // Check if the path component for this subpath already exists.
            let path_component_index = if let Some(existing_index) = Self::find_existing_subpath(
                &self.subpath_lookup,
                &self.path_components,
                &self.string_table,
                &self.strings,
                path_component,
                subpath_hash,
                parent_index,
            ) {
                // Make sure that
                // 1) we're not processing the leaf/file component
                // (because we can't have a new file with the same name as an existing file/folder);
                // ...
                if last {
                    return Err(FileOrFolderAlreadyExistsAtFilePath(
                        self.path_buf(existing_index).into(),
                    ));
                }

                // ...
                // 2) the subpath is not a path to an existing file
                // (because we can't have a new file/folder with the same name as an existing file);
                if self.path_lookup.contains_key(&subpath_hash) {
                    return Err(FileAlreadyExistsAtFileOrFolderPath(
                        self.path_buf(existing_index).into(),
                    ));
                }

                existing_index

            // If this subpath doesn't exist yet, we're going to add it.
            } else {
                let path_component_index = Self::add_path_component(
                    &mut self.string_lookup,
                    &mut self.string_table,
                    &mut self.strings,
                    &mut self.path_components,
                    &self.hash_builder,
                    path_component,
                    parent_index,
                    path_component_idx as NumComponents + 1,
                    string_len,
                );

                self.subpath_lookup
                    .insert(subpath_hash, path_component_index);

                path_component_index
            };

            // Update the parent index to the current path component index.
            parent_index.replace(path_component_index);

            if !last {
                string_len += 1;
            }
        }

        debug_assert_eq!(path_hash, hasher.finish());

        // Update the path lookup with the path component index for the leaf node.

        // Must succeed if we got here, or we'd error out above.
        let parent_index = unsafe { debug_unwrap(parent_index) };

        let _none = self.path_lookup.insert(
            path_hash,
            LeafPathComponent::new(parent_index, num_components, string_len),
        );
        // Must be `None`, or we'd error out above.
        debug_assert!(_none.is_none());

        Ok(path_hash)
    }

    /// Consumes the [`writer`](FileTreeWriter) and serializes its data to the writer `w`.
    /// Stores the user-provided "version" into the header.
    /// Produced data blob may then be used by the [`FileTreeReader`].
    pub fn write<W: Write>(self, version: u64, w: &mut W) -> Result<usize, io::Error> {
        let mut written = 0;

        // Header.
        let header = FileTreeHeader::new(
            self.path_lookup.len() as _,
            self.path_components.len() as _,
            self.string_table.len() as _,
            version,
        );

        written += header.write(w)?;

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Path lookup.

        // Get and sort the path hashes.
        let mut path_hashes = self.path_lookup.keys().cloned().collect::<Vec<_>>();
        path_hashes.sort();

        // Write the path hashes.
        for &path_hash in path_hashes.iter() {
            written += write_u64(w, path_hash)?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Write the leaf path components.
        for leaf_path_component in path_hashes
            .iter()
            // Must succeed - all keys are contained in the map.
            .map(|path_hash| *unsafe { debug_unwrap(self.path_lookup.get(path_hash)) })
        {
            written += leaf_path_component.write(w)?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Path components array.

        for path_component in self.path_components {
            written += path_component.path_component.write(w)?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // String table.

        // Patch up the string offsets to be relative to the start of the blob.
        let string_offset =
            (written + self.string_table.len() * size_of::<PackedInternedString>()) as StringOffset;

        for &offset_and_length in self.string_table.iter() {
            written += offset_and_length.write(w, string_offset)?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Strings.

        w.write_all(self.strings.as_bytes())?;
        written += self.strings.len();

        Ok(written as _)
    }

    /// Consumes the [`writer`](FileTreeWriter) and serializes its data to the byte vec.
    /// Stores the user-provided "version" into the header.
    /// Produced data blob may then be used by the [`FileTreeReader`].
    pub fn write_to_vec(self, version: u64) -> Result<Vec<u8>, io::Error> {
        let mut result = Vec::new();
        self.write(version, &mut result)?;
        result.shrink_to_fit();
        Ok(result)
    }

    /// Returns the number of [`file paths`](FilePath) [`inserted`](#method.insert) into the writer.
    pub fn len(&self) -> usize {
        self.path_lookup.len()
    }

    /// Returns the number of unique strings [`inserted`](#method.insert) into the writer.
    pub fn num_strings(&self) -> usize {
        self.string_table.len()
    }

    /// Returns the total length in bytes of all unique strings [`inserted`](#method.insert) into the writer.
    pub fn string_len(&self) -> usize {
        self.strings.len()
    }

    /// Clears the writer, resetting all internal data structures without deallocating any storage.
    pub fn clear(&mut self) {
        self.subpath_lookup.clear();
        self.string_lookup.clear();
        self.path_lookup.clear();
        self.path_components.clear();
        self.string_table.clear();
        self.strings.clear();
    }

    /// Returns the index of the existing path component with `subpath_hash` and the current component `path_component`, if one exists.
    /// The caller guarantees `parent_index` is valid, if `Some`.
    fn find_existing_subpath(
        subpath_lookup: &SubpathLookup,
        path_components: &[PathComponentAndMetadata],
        string_table: &[InternedString],
        strings: &String,
        path_component: FilePathComponent,
        subpath_hash: PathHash,
        parent_index: Option<PathComponentIndex>,
    ) -> Option<PathComponentIndex> {
        let mut result = None;

        if let Some(existing_indices) = subpath_lookup.get(&subpath_hash) {
            'indices: for &existing_index in existing_indices {
                debug_assert!((existing_index as usize) < path_components.len());
                let existing_path_component =
                    unsafe { *path_components.get_unchecked(existing_index as usize) };

                let mut existing_subpath = Self::iter_impl(
                    path_components,
                    string_table,
                    strings,
                    existing_path_component.path_component,
                    existing_path_component.num_components,
                );

                // Must succeed - empty paths are not allowed.
                let existing_path_component = unsafe { debug_unwrap(existing_subpath.next()) };

                if path_component != existing_path_component {
                    // New and existing path component strings mismatch.
                    debug_assert!(result.is_none());
                    continue 'indices;
                }

                if let Some(mut new_subpath) = parent_index.map(|parent_index| {
                    debug_assert!((parent_index as usize) < path_components.len());
                    let parent_path_component =
                        unsafe { *path_components.get_unchecked(parent_index as usize) };

                    Self::iter_impl(
                        path_components,
                        string_table,
                        strings,
                        parent_path_component.path_component,
                        parent_path_component.num_components,
                    )
                }) {
                    loop {
                        if let Some(existing_path_component) = existing_subpath.next() {
                            if let Some(new_path_component) = new_subpath.next() {
                                if new_path_component != existing_path_component {
                                    // New and existing path component strings mismatch.
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
                    // New and existing paths are the same length (one component).
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

    fn hash_string(mut hasher: H::Hasher, string: FilePathComponent) -> PathHash {
        hasher.write(string.as_bytes());
        hasher.finish()
    }

    /// Adds the unique `string` with `hash` to the lookup data structures and returns its index.
    ///
    /// The caller guarantees that `string` with `hash` has not been interned yet.
    fn intern_string(
        string_lookup: &mut StringLookup,
        string_table: &mut Vec<InternedString>,
        strings: &mut String,
        string: FilePathComponent,
        hash: PathHash,
    ) -> StringIndex {
        let offset_and_len = InternedString::new(strings.len() as _, string.len() as _);
        strings.push_str(string);
        let string_index = string_table.len() as _;
        string_table.push(offset_and_len);
        string_lookup.insert(hash, string_index);
        string_index
    }

    /// Returns the string index of the interned `string` in the string table, if it is interned,
    /// or interns it and returns its new index in the string table.
    ///
    /// The caller guarantees the `string` is not empty.
    fn interned_string_index(
        string_lookup: &mut StringLookup,
        string_table: &mut Vec<InternedString>,
        strings: &mut String,
        hasher: H::Hasher,
        string: FilePathComponent,
    ) -> StringIndex {
        // First hash the path component's string and check if was already added.
        let string_hash = Self::hash_string(hasher, string);

        if let Some(string_index) = string_lookup
            // First lookup by string hash.
            .get(&string_hash)
            // Then compare the strings.
            .map(|string_indices| {
                string_indices.iter().cloned().find(|string_index| {
                    string_impl(string_table, strings, *string_index) == string
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

    /// The caller guarantees the `path_component` with `parent_index` does not exist in the `path_components` array.
    fn add_path_component(
        string_lookup: &mut StringLookup,
        string_table: &mut Vec<InternedString>,
        strings: &mut String,
        path_components: &mut Vec<PathComponentAndMetadata>,
        hash_builder: &H,
        path_component: FilePathComponent,
        parent_index: Option<PathComponentIndex>,
        num_components: NumComponents,
        string_len: FullStringLength,
    ) -> PathComponentIndex {
        // Get / intern the path component's string index in the string table.
        let string_index = Self::interned_string_index(
            string_lookup,
            string_table,
            strings,
            hash_builder.build_hasher(),
            path_component,
        );

        // Add a new path component to the lookup array, using the current parent index, if any.
        let path_component = PathComponent::new(string_index, parent_index);

        #[cfg(debug_assertions)]
        {
            for path_component_ in path_components.iter() {
                debug_assert!(path_component_.path_component != path_component);
            }
        }

        let path_component_index = path_components.len() as _;
        debug_assert!(num_components > 0);
        path_components.push(PathComponentAndMetadata {
            path_component,
            num_components,
            string_len,
        });

        path_component_index
    }

    /// Returns a reverse (leaf to root) iterator over path components of the path starting with `path_component`.
    /// The caller guarantees the path ending with `path_component` actually has `num_components`.
    fn iter(
        &self,
        path_component: PathComponent,
        num_components: NumComponents,
    ) -> impl ExactSizeIterator<Item = FilePathComponent> {
        Self::iter_impl(
            &self.path_components,
            &self.string_table,
            &self.strings,
            path_component,
            num_components,
        )
    }

    /// Returns a reverse (leaf to root) iterator over path components of the path starting with `path_component`.
    /// The caller guarantees the path ending with `path_component` actually has `num_components`.
    fn iter_impl<'a>(
        path_components: &'a [PathComponentAndMetadata],
        string_table: &'a [InternedString],
        strings: &'a String,
        path_component: PathComponent,
        num_components: NumComponents,
    ) -> impl ExactSizeIterator<Item = &'a NonEmptyStr> {
        PathIter::new(
            path_components,
            string_table,
            strings,
            path_component,
            num_components,
        )
    }

    /// Used for error reporting.
    /// The caller guarantees the path component `index` is valid.
    fn path_buf(&self, index: PathComponentIndex) -> FilePathBuf {
        debug_assert!((index as usize) < self.path_components.len());
        let path_component = unsafe { *self.path_components.get_unchecked(index as usize) };

        let mut string = String::with_capacity(path_component.string_len as _);

        build_path_string(
            || self.iter(path_component.path_component, path_component.num_components),
            path_component.string_len,
            &mut string,
        );

        unsafe { FilePathBuf::new_unchecked(string) }
    }

    #[cfg(test)]
    fn lookup(&self, hash: PathHash) -> Option<FilePathBuf> {
        self.path_lookup
            .get(&hash)
            .map(|leaf_path_component| self.path_buf(leaf_path_component.path_component_index))
    }
}

/// The caller guarantees the string `index` is valid.
fn string_impl<'s>(
    string_table: &[InternedString],
    strings: &'s String,
    index: StringIndex,
) -> &'s NonEmptyStr {
    debug_assert!((index as usize) < string_table.len());
    let string = unsafe { string_table.get_unchecked(index as usize) };
    debug_assert!(string.offset < strings.len() as _);
    debug_assert!((string.offset + string.len as StringOffset) <= strings.len() as StringOffset);
    unsafe {
        NonEmptyStr::new_unchecked(strings.get_unchecked(
            string.offset as usize..(string.offset + string.len as StringOffset) as usize,
        ))
    }
}

struct PathIter<'a> {
    path_components: &'a [PathComponentAndMetadata],
    string_table: &'a [InternedString],
    strings: &'a String,
    current_component: Option<PathComponent>,
    num_components: NumComponents,
}

impl<'a> PathIter<'a> {
    fn new(
        path_components: &'a [PathComponentAndMetadata],
        string_table: &'a [InternedString],
        strings: &'a String,
        path_component: PathComponent,
        num_components: NumComponents,
    ) -> Self {
        Self {
            path_components,
            string_table,
            strings,
            current_component: Some(path_component),
            num_components,
        }
    }
}

impl<'a> Iterator for PathIter<'a> {
    type Item = &'a NonEmptyStr;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(path_component) = self.current_component.take() {
            let str = string_impl(self.string_table, self.strings, path_component.string_index);

            if let Some(parent_index) = path_component.parent_index {
                self.current_component
                    .replace(path_component_impl(self.path_components, parent_index));
            }

            debug_assert!(self.num_components > 0);
            self.num_components -= 1;

            Some(str)
        } else {
            debug_assert!(self.num_components == 0);

            None
        }
    }
}

impl<'a> ExactSizeIterator for PathIter<'a> {
    fn len(&self) -> usize {
        self.num_components as _
    }
}

/// The caller guarantees the path component `index` is valid.
fn path_component_impl(
    path_components: &[PathComponentAndMetadata],
    index: PathComponentIndex,
) -> PathComponent {
    debug_assert!((index as usize) < path_components.len());
    unsafe { path_components.get_unchecked(index as usize) }.path_component
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use {super::*, minifilepath_macro::filepath, seahash::SeaHasher};

    #[derive(Default)]
    struct BuildSeaHasher;

    impl BuildHasher for BuildSeaHasher {
        type Hasher = SeaHasher;

        fn build_hasher(&self) -> Self::Hasher {
            SeaHasher::new()
        }
    }

    #[test]
    fn FileOrFolderAlreadyExistsAtFilePath() {
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

            assert_eq!(writer.len(), 0);

            let foo_bar = writer.insert(filepath!("foo/bar")).unwrap();

            assert_eq!(writer.len(), 1);

            assert_eq!(
                writer.lookup(foo_bar).unwrap().as_str(),
                "foo/bar".to_string()
            );

            assert!(
                matches!(writer.insert(filepath!("foo")).err().unwrap(), FileTreeWriterError::FileOrFolderAlreadyExistsAtFilePath(x) if x == FilePathBuf::new("foo").unwrap())
            );
        }

        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

            let foo_bar_baz = writer.insert(filepath!("foo/bar/baz")).unwrap();

            assert_eq!(writer.lookup(foo_bar_baz).unwrap().as_str(), "foo/bar/baz");

            assert!(
                matches!(writer.insert(filepath!("foo/bar")).err().unwrap(), FileTreeWriterError::FileOrFolderAlreadyExistsAtFilePath(x) if x == FilePathBuf::new("foo/bar").unwrap())
            );
        }
    }

    #[test]
    fn FileAlreadyExistsAtFileOrFolderPath() {
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

            let foo = writer.insert(filepath!("foo")).unwrap();

            assert_eq!(writer.lookup(foo).unwrap().as_str(), "foo");

            assert!(
                matches!(writer.insert(filepath!("foo/bar")).err().unwrap(), FileTreeWriterError::FileAlreadyExistsAtFileOrFolderPath(x) if x == FilePathBuf::new("foo").unwrap())
            );
        }

        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

            let foo_bar = writer.insert(filepath!("foo/bar")).unwrap();

            assert_eq!(writer.lookup(foo_bar).unwrap().as_str(), "foo/bar");

            assert!(
                matches!(writer.insert(filepath!("foo/bar/baz")).err().unwrap(), FileTreeWriterError::FileAlreadyExistsAtFileOrFolderPath(x) if x == FilePathBuf::new("foo/bar").unwrap())
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

            let fo_o = writer.insert(filepath!("fo/o")).unwrap();

            assert_eq!(writer.lookup(fo_o).unwrap().as_str(), "fo/o");

            assert!(
                matches!(writer.insert(filepath!("f/oo")).err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x == FilePathBuf::new("fo/o").unwrap())
            );
        }

        {
            let mut writer = FileTreeWriter::new(BuildFNV1aHasher);

            let cost_arring = writer.insert(filepath!("cost/arring")).unwrap();

            assert_eq!(writer.lookup(cost_arring).unwrap().as_str(), "cost/arring");

            assert!(
                matches!(writer.insert(filepath!("liq/uid")).err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x == FilePathBuf::new("cost/arring").unwrap())
            );
        }

        {
            let mut writer = FileTreeWriter::new(BuildFNV1aHasher);

            let altarag_es = writer.insert(filepath!("altarag/es")).unwrap();

            assert_eq!(writer.lookup(altarag_es).unwrap().as_str(), "altarag/es");

            assert!(
                matches!(writer.insert(filepath!("zink/es")).err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x == FilePathBuf::new("altarag/es").unwrap())
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

                let foo_bar_baz = writer.insert(filepath!("foo/bar/baz")).unwrap();
                assert_eq!(foo_bar_baz, 3);
                assert_eq!(writer.lookup(foo_bar_baz).unwrap().as_str(), "foo/bar/baz");

                let bar = writer.insert(filepath!("bar")).unwrap();
                assert_eq!(bar, 2);
                assert_eq!(writer.lookup(bar).unwrap().as_str(), "bar");
            }

            {
                let mut writer = FileTreeWriter::new(BuildMockHasher);

                let foo_bar_baz = writer.insert(filepath!("foo/bar/baz")).unwrap();
                assert_eq!(foo_bar_baz, 3);
                assert_eq!(writer.lookup(foo_bar_baz).unwrap().as_str(), "foo/bar/baz");

                let bob_foo_bar = writer.insert(filepath!("bob/foo/bar")).unwrap();
                assert_eq!(bob_foo_bar, 2);
                assert_eq!(writer.lookup(bob_foo_bar).unwrap().as_str(), "bob/foo/bar");
            }

            {
                let mut writer = FileTreeWriter::new(BuildMockHasher);

                let foo_bar_baz = writer.insert(filepath!("foo/bar/baz")).unwrap();
                assert_eq!(foo_bar_baz, 3);
                assert_eq!(writer.lookup(foo_bar_baz).unwrap().as_str(), "foo/bar/baz");

                let foo_bill = writer.insert(filepath!("foo/bill")).unwrap();
                assert_eq!(foo_bill, 2);
                assert_eq!(writer.lookup(foo_bill).unwrap().as_str(), "foo/bill");
            }
        }
    }
}

use {
    crate::*,
    minifilepath::*,
    ministr::*,
    std::{
        collections::HashMap,
        hash::{BuildHasher, Hash, Hasher},
        io::{self, Write},
        iter::Iterator,
        mem::size_of,
    },
};

type PathComponents = Vec<PathComponent>;

/// Here the `PathHash` key is the hash of the entire path.
/// `HashMap` and not a `MultiMap` because we don't allow hash collisions for leaf file paths.
/// NOTE: need to store the full `LeafPathComponent` in the leaf lookup, because even though we are guaranteed
/// to never have hash collisions between leaf paths (as we don't allow them), we might have hash collisions
/// between leaf paths and subpaths, so can't rely on `SubpathLookup` to only contain only one entry for the leaf path hash.
type PathLookup = HashMap<PathHash, LeafPathComponent>;

/// Here the `PathHash` key is the accumulated hash of the entire subpath so far.
type SubpathLookup = MultiMap<PathHash, SubpathComponent>;

/// Here the `PathHash` key is the hash of just a single path component.
type StringLookup = MultiMap<PathHash, StringIndex>;

type StringTable = Vec<InternedString>;

/// Need to disambiguate between subpath components for extensions / file stems
/// (to correctly handle `FolderAlreadyExistsAtFilePath` / `FileAlreadyExistsAtFolderPath` errors,
/// but still allow file stem subpaths to be reused)
/// and everything else.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SubpathComponentType {
    Extension,
    FileStem,
    FileOrFolderName,
}

/// Like `LeafPathComponent`, but
/// 1) doesn't need `num_components`, and
/// 2) needs more precise `component_type` instead of just an `is_extension` flag.
#[derive(Clone, Copy, PartialEq, Eq)]
struct SubpathComponent {
    path_component_index: PathComponentIndex,
    string_len: FullStringLength,
    component_type: SubpathComponentType,
}

/// Provides an API to append [`hashed`](PathHash) [`file paths`](FilePath) to a lookup data structure and store them space-efficiently.
/// Deduplicates unique [`path component`](FilePathComponent) strings (including extensions) and file tree nodes.
///
/// When finished, [`writes`](FileTreeWriter::write) the data to a binary blob which may then be saved, read by a [`FileTreeReader`]
/// and used to lookup the full file paths by their hashes.
///
/// Uses a user-provided [`hasher builder`](std::hash::BuildHasher) to hash the path components.
pub struct FileTreeWriter<H: BuildHasher> {
    /// User-provided hasher builder used to build the hasher which is used to hash the paths.
    hash_builder: H,
    /// Persistent array of valid path components added so far.
    /// Indexed into by entries of `subpath_lookup` and `path_lookup`.
    ///
    /// Needed by the writer and serialized to the data blob.
    path_components: PathComponents,
    /// Persistent lookup map from a full file path hash to its leaf path component.
    ///
    /// Needed by the writer and serialized to the data blob.
    path_lookup: PathLookup,
    /// Temporary lookup map from each valid subpath hash added so far to its index
    /// (or indices, if there's subpath string hash collisions) in the `path_components` array.
    ///
    /// Needed only by the writer, not serialized to the data blob.
    subpath_lookup: SubpathLookup,
    /// Temporary lookup map from a single path component string's hash to its index
    /// (or indices, if there's subpath string hash collisions) in the `string_table`.
    ///
    /// Needed only by the writer, not serialized to the data blob.
    string_lookup: StringLookup,
    /// Persistent array of unique string offsets and lengths in the `strings` buffer.
    ///
    /// Needed by the writer and serialized to the data blob.
    string_table: StringTable,
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
            path_components: Vec::new(),
            path_lookup: PathLookup::new(),
            subpath_lookup: SubpathLookup::new(),
            string_lookup: StringLookup::new(),
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

        // Count the number of components, and hash the path fully to determine straight up if we have a path hash collision
        // (or the same path is being inserted more then once).
        // Need to preprocess to avoid inserting strings / subpaths into the lookup if the path is ultimately found to be invalid.
        // NOTE: file extension, if any, will be treated as an additional component later.
        let (num_components, path_hash) = {
            let mut hasher = self.hash_builder.build_hasher();
            let mut num_components: NumComponents = 0;

            for path_component in path.components() {
                hasher.write(path_component.as_bytes());
                num_components += 1;
            }

            debug_assert!(num_components > 0, "valid file paths are not empty");

            let path_hash = hasher.finish();

            // Sanity check. Make sure the `Hash` implementation for the path hash actually behaves as we expect it to.
            {
                let mut _hasher = self.hash_builder.build_hasher();
                path.hash(&mut _hasher);
                let _path_hash = _hasher.finish();
                debug_assert_eq!(path_hash, _path_hash);
            }

            (num_components, path_hash)
        };

        // Check for already added paths and file path hash collisions.
        if let Some(&lpc) = self.path_lookup.get(&path_hash) {
            if self
                .iter(lpc.path_component_index, lpc.is_extension)
                .eq(file_path_iter(path))
            {
                return Err(FileTreeWriterError::PathAlreadyExists);
            } else {
                return Err(FileTreeWriterError::PathHashCollision(self.path_buf(
                    lpc.path_component_index,
                    lpc.string_len,
                    lpc.is_extension,
                )));
            }
        }

        let mut hasher = self.hash_builder.build_hasher();
        // Separate hasher needed to hash file name stems without the extension (if any) to reuse certain subpaths
        // (e.g. reuse "foo/bar" when "foo/bar.txt" already exists).
        let mut file_stem_hasher = self.hash_builder.build_hasher();

        // Index of the parent path component for each processed path component in the loop below;
        // index of the leaf/file path component after the last one was processed.
        let mut parent_index = None;
        let mut string_len: FullStringLength = 0;

        let mut has_extension = false;

        for (path_component_idx, path_component) in path.components().enumerate() {
            // If it's the last path component, it must be the name of a file
            // (and thus no other file/folder is allowed to exist at that path).
            let last = path_component_idx == (num_components - 1) as _;

            string_len += path_component.len() as FullStringLength;

            // Hash the subpath so far.
            hasher.write(path_component.as_bytes());
            let subpath_hash = hasher.finish();

            // Check if the path component / file tree node for this subpath already exists
            // (including file stems reused for new folder names).
            let (path_component_index, _has_extension) = if let Some(spc) =
                self.find_existing_subpath(subpath_hash, path_component, parent_index, last)
            {
                // Make sure that
                // 1) we're not processing the leaf/file component
                // (because we can't have a new file with the same name as an existing folder
                // (NOTE: can't be an existing file, because we'd error out above on a full path hash check))
                // (unless we reused a file stem component, which is OK (e.g. we had "foo/bar.txt" and inserted "foo/bar"));
                // ...
                if last {
                    if spc.component_type != SubpathComponentType::FileStem {
                        debug_assert!(!self.path_lookup.contains_key(&subpath_hash));
                        return Err(FolderAlreadyExistsAtFilePath);
                    }
                }
                // ...
                // 2) the subpath is not a path to an existing file
                // (because we can't have a new folder with the same name as an existing file);
                else if self.path_lookup.contains_key(&subpath_hash) {
                    //return Err(FileAlreadyExistsAtFolderPath(self.path_buf(spc).into()));
                    return Err(FileAlreadyExistsAtFolderPath(
                        self.path_buf(
                            spc.path_component_index,
                            spc.string_len,
                            spc.component_type == SubpathComponentType::Extension,
                        )
                        .into(),
                    ));
                }

                // Update the file stem hasher with the full path component string to get it up to date with the subpath hasher.
                file_stem_hasher.write(path_component.as_bytes());
                debug_assert_eq!(hasher.finish(), file_stem_hasher.finish());

                (spc.path_component_index, false)

            // If this subpath doesn't exist yet, we're going to add it.
            } else {
                self.add_path_component(
                    subpath_hash,
                    path_component,
                    parent_index,
                    last,
                    string_len,
                    &mut file_stem_hasher,
                )
            };

            // Update the parent index to the current path component index.
            parent_index.replace(path_component_index);

            // Account for the path component separator in the total string length.
            if !last {
                string_len += 1;
            } else {
                has_extension = _has_extension;
            }
        }

        debug_assert_eq!(path_hash, hasher.finish());
        debug_assert_eq!(path_hash, file_stem_hasher.finish());

        // Update the leaf path components.

        // Must succeed if we got here, or we'd error out above.
        let parent_index = unsafe { debug_unwrap(parent_index) };

        let _none = self.path_lookup.insert(
            path_hash,
            LeafPathComponent::new(
                parent_index,
                // Account for the extra path component for the extension.
                if has_extension {
                    num_components + 1
                } else {
                    num_components
                },
                string_len,
                has_extension,
            ),
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
            written += path_component.write(w)?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // String table.

        // Patch up the string offsets to be relative to the start of the blob.
        let string_offset =
            (written + self.string_table.len() * size_of::<PackedInternedString>()) as StringOffset;

        for offset_and_length in self.string_table.iter() {
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

    /// Attempts to fill the `builder` with the [`file path`](FilePathBuf) associated with the file path `hash`, if any.
    ///
    /// Returns the `builder` back if the path `hash` does not have a [`file path`](FilePathBuf) associated with it.
    pub fn lookup_into(
        &self,
        hash: PathHash,
        builder: FilePathBuilder,
    ) -> Result<FilePathBuf, FilePathBuilder> {
        if let Some(&lpc) = self.path_lookup.get(&hash) {
            Ok(self.build_path_string(
                lpc.path_component_index,
                lpc.string_len,
                lpc.is_extension,
                builder,
            ))
        } else {
            Err(builder)
        }
    }

    /// Returns the [`file path`](FilePathBuf) associated with the file path `hash`, if any.
    pub fn lookup(&self, hash: PathHash) -> Option<FilePathBuf> {
        self.lookup_into(hash, FilePathBuilder::new()).ok()
    }

    /// Returns an existing subpath component, if any,
    /// matching (the string of) the currently processed new subpath starting (in reverse) with `path_component`,
    /// with `parent_index` parent (if any).
    /// `subpath_hash` is the hash of the new subpath so far (including `path_component`).
    /// `last` is true if this is the file name (i.e. leaf / last) component of the new path.
    fn find_existing_subpath(
        &self,
        subpath_hash: PathHash,
        path_component: FilePathComponent<'_>,
        parent_index: Option<PathComponentIndex>,
        last: bool,
    ) -> Option<SubpathComponent> {
        self.subpath_lookup
            .get(&subpath_hash)
            .map(|existing_path_components| {
                for &existing_path_component in existing_path_components {
                    let existing_path = self.iter(
                        existing_path_component.path_component_index,
                        existing_path_component.component_type == SubpathComponentType::Extension,
                    );
                    let new_path = self.new_path_iter(path_component, parent_index, last);

                    match existing_path.file_name {
                        // Existing (sub)path is to a file extension.
                        FileName::WithExtension {
                            extension: existing_extension,
                            file_stem: existing_file_stem,
                        } => {
                            debug_assert!(self.path_lookup.contains_key(&subpath_hash));

                            match new_path.file_name {
                                // New (sub)path is to a file extension - compare the strings directly.
                                FileName::WithExtension {
                                    extension: new_extension,
                                    file_stem: new_file_stem,
                                } => {
                                    if new_extension != existing_extension
                                        || new_file_stem != existing_file_stem
                                    {
                                        continue;
                                    }
                                }
                                // New subpath is to a folder or file name (with no extension).
                                FileName::NoExtension(new_file_name) => {
                                    // Check the case where the new file or folder name string
                                    // has the same form as the existing path file name with an extension.
                                    //
                                    // E.g.: new subpath is "foo/bar.txt/..." (`new_file_name` == "bar.txt"),
                                    // existing (sub)path is "foo/bar.txt" (`file_stem` == "bar", `extension` == "txt").
                                    // This must successfully match the subpath and return a `FileAlreadyExistsAtFolderPath` error.
                                    if let Some(FileStemAndExtension {
                                        extension: new_extension,
                                        file_stem: new_file_stem,
                                    }) = file_stem_and_extension(new_file_name)
                                    {
                                        if new_extension != existing_extension
                                            || new_file_stem != existing_file_stem
                                        {
                                            continue;
                                        }
                                    // New file or folder name string does not have an "extension", so strings definitely don't match.
                                    } else {
                                        continue;
                                    }
                                }
                            }
                        }
                        // Existing subpath is to a folder or file name (with no extension).
                        FileName::NoExtension(existing_file_or_folder_name) => {
                            match new_path.file_name {
                                // New (sub)path is to a file extension.
                                FileName::WithExtension {
                                    file_stem: new_file_stem,
                                    extension: new_extension,
                                } => {
                                    // Check the case where the existing file or folder name string
                                    // has the same form as the new path file name with an extension.
                                    //
                                    // E.g.: existing subpath is "foo/bar.txt/..." (`file_or_folder_name` == "bar.txt"),
                                    // new (sub)path is "foo/bar.txt" (`file_stem` == "bar", `extension` == "txt").
                                    // This must successfully match the subpath and return a `FolderAlreadyExistsAtFilePath` error.
                                    if let Some(FileStemAndExtension {
                                        file_stem,
                                        extension,
                                    }) = file_stem_and_extension(existing_file_or_folder_name)
                                    {
                                        if new_extension != extension || new_file_stem != file_stem
                                        {
                                            continue;
                                        }
                                    // Existing file or folder name string does not have an "extension", so strings definitely don't match.
                                    } else {
                                        continue;
                                    }
                                }
                                // New subpath is to a folder or file name (with no extension) - compare the strings directly.
                                FileName::NoExtension(new_file_or_folder_name) => {
                                    if existing_file_or_folder_name != new_file_or_folder_name {
                                        continue;
                                    }
                                }
                            }
                        }
                    }

                    // Compare the rest of the file paths.
                    if existing_path.file_path.eq(new_path.file_path) {
                        return Some(existing_path_component);
                    }
                }

                None
            })
            .flatten()
    }

    /// Adds the new unique `path_component` with `parent_index` parent (if any)
    /// to the lookup structures.
    /// `subpath_hash` is the hash of the new subpath so far (including `path_component`).
    /// `last` is true if this is the file name (i.e. leaf / last) component of the new path.
    /// `string_len` is the full length of the file path string so far, separators included.
    fn add_path_component(
        &mut self,
        subpath_hash: PathHash,
        path_component: FilePathComponent<'_>,
        parent_index: Option<PathComponentIndex>,
        last: bool,
        string_len: FullStringLength,
        file_stem_hasher: &mut H::Hasher,
    ) -> (PathComponentIndex, bool) {
        let add_path_component_impl = |path_components: &mut PathComponents,
                                       subpath_lookup: &mut SubpathLookup,
                                       string_lookup: &mut StringLookup,
                                       string_table: &mut StringTable,
                                       strings: &mut String,
                                       hasher: H::Hasher,
                                       subpath_hash: PathHash,
                                       path_component: &str,
                                       parent_index: Option<PathComponentIndex>,
                                       string_len: FullStringLength,
                                       component_type: SubpathComponentType|
         -> PathComponentIndex {
            // Add the new path component to the lookup array, using the current parent index, if any.
            let path_component =
            // Get / intern the path component's string index in the string table.
            PathComponent::new(Self::interned_string_index(
                string_lookup,
                string_table,
                strings,
                path_component,
                hasher,
            ), parent_index);

            // All path components must be unique.
            #[cfg(debug_assertions)]
            {
                for &path_component_ in path_components.iter() {
                    debug_assert!(path_component_ != path_component);
                }
            }

            let path_component_index = path_components.len() as PathComponentIndex;
            path_components.push(path_component);

            subpath_lookup.insert(
                subpath_hash,
                SubpathComponent {
                    path_component_index,
                    string_len,
                    component_type,
                },
            );

            path_component_index
        };

        match file_stem_and_extension(path_component) {
            // Path component is a file name with an extension - insert two path components, for the file stem and the extension.
            // Return the index of the extension path component.
            Some(FileStemAndExtension {
                file_stem,
                extension,
            }) if last => {
                let file_stem_str = file_stem.map(NonEmptyStr::as_str).unwrap_or("");

                file_stem_hasher.write(file_stem_str.as_bytes());
                let file_stem_hash = file_stem_hasher.finish();

                // Account for the extension string length (including the extension separator) for the file stem string length.
                let extension_string_len = (extension.len() + 1) as FullStringLength;
                debug_assert!(string_len >= extension_string_len);

                let file_stem_path_component_index = add_path_component_impl(
                    &mut self.path_components,
                    &mut self.subpath_lookup,
                    &mut self.string_lookup,
                    &mut self.string_table,
                    &mut self.strings,
                    self.hash_builder.build_hasher(),
                    file_stem_hash,
                    file_stem_str,
                    parent_index,
                    string_len - extension_string_len,
                    SubpathComponentType::FileStem,
                );

                let extension_path_component_index = add_path_component_impl(
                    &mut self.path_components,
                    &mut self.subpath_lookup,
                    &mut self.string_lookup,
                    &mut self.string_table,
                    &mut self.strings,
                    self.hash_builder.build_hasher(),
                    subpath_hash,
                    extension,
                    Some(file_stem_path_component_index),
                    string_len,
                    SubpathComponentType::Extension,
                );

                // Update the file stem hasher with the extension to keep it up to date with the subpath hasher.
                file_stem_hasher.write(".".as_bytes());
                file_stem_hasher.write(extension.as_bytes());
                debug_assert_eq!(file_stem_hasher.finish(), subpath_hash);

                (extension_path_component_index, true)
            }
            // Path component is a folder name, or doesn't have an extension - insert one path component, for the folder / file name.
            // Return the index of the path component.
            None | Some(_) => {
                let file_or_folder_name_component_index = add_path_component_impl(
                    &mut self.path_components,
                    &mut self.subpath_lookup,
                    &mut self.string_lookup,
                    &mut self.string_table,
                    &mut self.strings,
                    self.hash_builder.build_hasher(),
                    subpath_hash,
                    path_component,
                    parent_index,
                    string_len,
                    SubpathComponentType::FileOrFolderName,
                );

                // Update the file stem hasher with the entire path components to keep it up to date with the subpath hasher.
                file_stem_hasher.write(path_component.as_bytes());
                debug_assert_eq!(file_stem_hasher.finish(), subpath_hash);

                (file_or_folder_name_component_index, false)
            }
        }
    }

    /// Returns a (reverse) file path iterator for the path component at `index`.
    /// The caller guarantees the path component `index` is valid.
    fn iter(
        &self,
        index: PathComponentIndex,
        is_extension: bool,
    ) -> FilePathIter<'_, impl Iterator<Item = FilePathComponent<'_>>> {
        let mut path_component = path_component_impl(&self.path_components, index);

        let file_name = if is_extension {
            // Extensions may not be empty.
            let extension = non_empty_string_impl(
                &self.string_table,
                &self.strings,
                path_component.string_index,
            );
            // Leaf path components with an extension have a parent component (file stem).
            let parent_index = unsafe { debug_unwrap(path_component.parent_index) };
            path_component = path_component_impl(&self.path_components, parent_index);
            // File stems may be empty.
            let file_stem = NonEmptyStr::new(string_impl(
                &self.string_table,
                &self.strings,
                path_component.string_index,
            ));

            FileName::WithExtension {
                extension,
                file_stem,
            }
        } else {
            // File names (with no extension) may not be empty.
            FileName::NoExtension(non_empty_string_impl(
                &self.string_table,
                &self.strings,
                path_component.string_index,
            ))
        };

        FilePathIter {
            file_name,
            file_path: PathIter::new(
                &self.path_components,
                &self.string_table,
                &self.strings,
                path_component
                    .parent_index
                    .map(|parent_index| path_component_impl(&self.path_components, parent_index)),
            ),
        }
    }

    /// Returns a (reverse) file path iterator for `cur_component` with `parent_index`.
    /// The caller guarantees the `parent_index` is valid.
    fn new_path_iter<'a>(
        &'a self,
        cur_component: FilePathComponent<'a>,
        parent_index: Option<PathComponentIndex>,
        last: bool,
    ) -> FilePathIter<'_, impl Iterator<Item = FilePathComponent<'a>>> {
        let file_name = if last {
            if let Some(FileStemAndExtension {
                file_stem,
                extension,
            }) = file_stem_and_extension(cur_component)
            {
                FileName::WithExtension {
                    extension,
                    file_stem,
                }
            } else {
                FileName::NoExtension(cur_component)
            }
        } else {
            FileName::NoExtension(cur_component)
        };

        FilePathIter {
            file_name,
            file_path: PathIter::new(
                &self.path_components,
                &self.string_table,
                &self.strings,
                parent_index
                    .map(|parent_index| path_component_impl(&self.path_components, parent_index)),
            ),
        }
    }

    /// Used for error reporting.
    /// The caller guarantees the path component `index` is valid.
    fn path_buf(
        &self,
        index: PathComponentIndex,
        string_len: FullStringLength,
        is_extension: bool,
    ) -> FilePathBuf {
        self.build_path_string(index, string_len, is_extension, FilePathBuilder::new())
    }

    /// The caller guarantees the path component `index` is valid,
    /// and that `string_len` matches the actual string length.
    fn build_path_string(
        &self,
        index: PathComponentIndex,
        string_len: FullStringLength,
        is_extension: bool,
        builder: FilePathBuilder,
    ) -> FilePathBuf {
        let mut string = builder.into_inner();
        build_path_string(self.iter(index, is_extension), string_len, &mut string);
        debug_assert!(!string.is_empty());
        unsafe { FilePathBuf::new_unchecked(string) }
    }

    /// Returns the string index of the interned `string` in the string table, if it is interned,
    /// or interns it and returns its new index in the string table.
    fn interned_string_index(
        string_lookup: &mut StringLookup,
        string_table: &mut StringTable,
        strings: &mut String,
        string: &str,
        mut hasher: H::Hasher,
    ) -> StringIndex {
        // First hash the path component's string and check if was already added.
        hasher.write(string.as_bytes());
        let string_hash = hasher.finish();

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

    /// Adds the unique `string` with `hash` to the lookup data structures and returns its index.
    ///
    /// The caller guarantees that `string` with `hash` has not been interned yet.
    fn intern_string(
        string_lookup: &mut StringLookup,
        string_table: &mut StringTable,
        strings: &mut String,
        string: &str,
        hash: PathHash,
    ) -> StringIndex {
        let offset_and_len = InternedString::new(
            // Force offset `0` for empty strings.
            if string.is_empty() { 0 } else { strings.len() } as _,
            string.len() as _,
        );
        strings.push_str(string);
        let string_index = string_table.len() as _;
        string_table.push(offset_and_len);
        string_lookup.insert(hash, string_index);
        string_index
    }
}

/// The caller guarantees the path component `index` is valid.
fn path_component_impl(
    path_components: &[PathComponent],
    index: PathComponentIndex,
) -> PathComponent {
    debug_assert!((index as usize) < path_components.len());
    unsafe { *path_components.get_unchecked(index as usize) }
}

/// The caller guarantees the string `index` is valid.
fn string_impl<'s>(
    string_table: &[InternedString],
    strings: &'s String,
    index: StringIndex,
) -> &'s str {
    debug_assert!((index as usize) < string_table.len());
    let string = unsafe { string_table.get_unchecked(index as usize) };
    debug_assert!((string.offset + string.len as StringOffset) <= strings.len() as StringOffset);
    unsafe {
        strings.get_unchecked(
            string.offset as usize..(string.offset + string.len as StringOffset) as usize,
        )
    }
}

/// The caller guarantees the string `index` is valid,
/// and that the string at `index` is non-empty (file stems may be empty).
fn non_empty_string_impl<'s>(
    string_table: &[InternedString],
    strings: &'s String,
    index: StringIndex,
) -> &'s NonEmptyStr {
    let string = string_impl(string_table, strings, index);
    debug_assert!(!string.is_empty());
    unsafe { NonEmptyStr::new_unchecked(string) }
}

struct PathIter<'a> {
    path_components: &'a [PathComponent],
    string_table: &'a [InternedString],
    strings: &'a String,
    cur_component: Option<PathComponent>,
}

impl<'a> PathIter<'a> {
    fn new(
        path_components: &'a [PathComponent],
        string_table: &'a [InternedString],
        strings: &'a String,
        cur_component: Option<PathComponent>,
    ) -> Self {
        Self {
            path_components,
            string_table,
            strings,
            cur_component,
        }
    }
}

impl<'a> Iterator for PathIter<'a> {
    type Item = FilePathComponent<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.cur_component.take().map(|cur_component| {
            if let Some(parent_index) = cur_component.parent_index {
                self.cur_component
                    .replace(path_component_impl(self.path_components, parent_index));
            }
            non_empty_string_impl(self.string_table, self.strings, cur_component.string_index)
        })
    }
}

/// Returns a (reverse) file path iterator for the components of `path`.
fn file_path_iter(
    path: &FilePath,
) -> FilePathIter<'_, impl Iterator<Item = FilePathComponent<'_>>> {
    let mut components = path.components().rev();
    // Empty paths are invalid.
    let file_name = unsafe { debug_unwrap(components.next()) };

    FilePathIter {
        file_name: if let Some(FileStemAndExtension {
            file_stem,
            extension,
        }) = file_stem_and_extension(file_name)
        {
            FileName::WithExtension {
                extension,
                file_stem,
            }
        } else {
            FileName::NoExtension(file_name)
        },
        file_path: components,
    }
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
    fn FolderAlreadyExistsAtFilePath() {
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar")).unwrap();
            assert_eq!(
                writer.insert(filepath!("foo")).err().unwrap(),
                FileTreeWriterError::FolderAlreadyExistsAtFilePath
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar/baz")).unwrap();
            assert_eq!(
                writer.insert(filepath!("foo/bar")).err().unwrap(),
                FileTreeWriterError::FolderAlreadyExistsAtFilePath
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar/baz.txt")).unwrap();
            assert_eq!(
                writer.insert(filepath!("foo/bar")).err().unwrap(),
                FileTreeWriterError::FolderAlreadyExistsAtFilePath
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar.txt/baz")).unwrap();
            assert_eq!(
                writer.insert(filepath!("foo/bar.txt")).err().unwrap(),
                FileTreeWriterError::FolderAlreadyExistsAtFilePath
            );
        }
    }

    #[test]
    fn FileAlreadyExistsAtFolderPath() {
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo")).unwrap();
            assert!(
                matches!(writer.insert(filepath!("foo/bar")).err().unwrap(), FileTreeWriterError::FileAlreadyExistsAtFolderPath(x) if x.as_file_path() == filepath!("foo"))
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar")).unwrap();
            assert!(
                matches!(writer.insert(filepath!("foo/bar/baz")).err().unwrap(), FileTreeWriterError::FileAlreadyExistsAtFolderPath(x) if x.as_file_path() == filepath!("foo/bar"))
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar.txt")).unwrap();
            assert!(
                matches!(writer.insert(filepath!("foo/bar.txt/baz")).err().unwrap(), FileTreeWriterError::FileAlreadyExistsAtFolderPath(x) if x.as_file_path() == filepath!("foo/bar.txt"))
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
    fn PathAlreadyExists() {
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo")).unwrap();
            assert_eq!(
                writer.insert(filepath!("foo")).err().unwrap(),
                FileTreeWriterError::PathAlreadyExists
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar.txt")).unwrap();
            assert_eq!(
                writer.insert(filepath!("foo/bar.txt")).err().unwrap(),
                FileTreeWriterError::PathAlreadyExists
            );
        }
    }

    #[test]
    fn PathHashCollision() {
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("fo/o")).unwrap();
            assert!(
                matches!(writer.insert(filepath!("f/oo")).err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x.as_file_path() == filepath!("fo/o"))
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildFNV1aHasher);
            writer.insert(filepath!("cost/arring")).unwrap();
            assert!(
                matches!(writer.insert(filepath!("liq/uid")).err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x.as_file_path() == filepath!("cost/arring"))
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildFNV1aHasher);
            writer.insert(filepath!("altarag/es")).unwrap();
            assert!(
                matches!(writer.insert(filepath!("zink/es")).err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x.as_file_path() == filepath!("altarag/es"))
            );
        }

        {
            // But this should work.

            // "foo/bar/baz"
            //   1 / 2 / 3 -> 3
            // "bar"
            //   2 -> 2 <== hash collision, shorter new path
            // "bob/foo/bar"
            //   4   1   2 -> 2 <== hash collision, longer new path
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

                // [1, 2, 3] -> 3
                let foo_bar_baz = writer.insert(filepath!("foo/bar/baz")).unwrap();
                assert_eq!(foo_bar_baz, 3);
                assert_eq!(writer.lookup(foo_bar_baz).unwrap().as_str(), "foo/bar/baz");

                // [2] -> 2
                let bar = writer.insert(filepath!("bar")).unwrap();
                assert_eq!(bar, 2);
                assert_eq!(writer.lookup(bar).unwrap().as_str(), "bar");
            }

            {
                let mut writer = FileTreeWriter::new(BuildMockHasher);

                // [1, 2, 3] -> 3
                let foo_bar_baz = writer.insert(filepath!("foo/bar/baz")).unwrap();
                assert_eq!(foo_bar_baz, 3);
                assert_eq!(writer.lookup(foo_bar_baz).unwrap().as_str(), "foo/bar/baz");

                // [4, 1, 2] -> 2
                let bob_foo_bar = writer.insert(filepath!("bob/foo/bar")).unwrap();
                assert_eq!(bob_foo_bar, 2);
                assert_eq!(writer.lookup(bob_foo_bar).unwrap().as_str(), "bob/foo/bar");
            }

            {
                let mut writer = FileTreeWriter::new(BuildMockHasher);

                // [1, 2, 3] -> 3
                let foo_bar_baz = writer.insert(filepath!("foo/bar/baz")).unwrap();
                assert_eq!(foo_bar_baz, 3);
                assert_eq!(writer.lookup(foo_bar_baz).unwrap().as_str(), "foo/bar/baz");

                // [1, 2] -> 2
                let foo_bill = writer.insert(filepath!("foo/bill")).unwrap();
                assert_eq!(foo_bill, 2);
                assert_eq!(writer.lookup(foo_bill).unwrap().as_str(), "foo/bill");
            }

            {
                let mut writer = FileTreeWriter::new(BuildMockHasher);

                // [1, 2] -> 2
                let foo_bar = writer.insert(filepath!("foo/bar")).unwrap();
                assert_eq!(foo_bar, 2);
                assert_eq!(writer.lookup(foo_bar).unwrap().as_str(), "foo/bar");

                // [1, 2] -> 2
                assert!(
                    matches!(writer.insert(filepath!("foo/bill")).err().unwrap(), FileTreeWriterError::PathHashCollision(x) if x == FilePathBuf::new("foo/bar").unwrap())
                );
            }
        }
    }

    #[test]
    fn writer() {
        use minifilepath_macro::filepath;

        let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

        assert_eq!(writer.len(), 0);

        let paths = &[
            filepath!("foo/bar/baz.cfg"),
            filepath!("foo/bar/.cfg"),
            filepath!("foo/bar/baz"),
            filepath!("fOO/bar/bill.txt"),
            filepath!("fOO/bar/bob.cfg"),
            filepath!("foo/bAr/bar"),
            filepath!("Bar"),
        ];

        let hashes = paths
            .iter()
            .map(|path| writer.insert(path).unwrap())
            .collect::<Vec<_>>();

        assert_eq!(writer.len(), hashes.len());

        let mut builder = FilePathBuilder::new();

        for (idx, hash) in hashes.iter().enumerate() {
            let result = writer.lookup_into(*hash, builder).unwrap();

            assert_eq!(result, writer.lookup(*hash).unwrap());
            assert_eq!(result.as_file_path(), paths[idx]);

            builder = result.into_builder();
        }
    }
}

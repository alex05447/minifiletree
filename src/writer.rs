#![allow(non_upper_case_globals)]

use {
    crate::*,
    bitflags::*,
    minifilepath::*,
    minimultimap::*,
    ministr::*,
    std::{
        collections::HashMap,
        hash::{BuildHasher, Hash, Hasher},
        io::{self, Write},
        iter::{self, Iterator},
        mem::size_of,
    },
};

/// Used to keep track of inserted file names.
/// Here the `PathHash` key is the full hash of the entire file path.
///
/// The hash is obtained by hashing path components (treating the file name as having no extension).
/// E.g. the path "foo/bar.txt" is hashed as a sequence of strings `[ "foo", "bar.txt" ]`.
/// NOTE - this is different from the subpath hash used in `SubpathLookup`, which would be hashed as `[ "foo", "bar", "txt" ]`.
///
/// `HashMap` and not a `MultiMap` because we don't allow hash collisions for leaf file paths.
/// NOTE: need to store the full `LeafPathComponent` in the leaf lookup, because even though we are guaranteed
/// to never have hash collisions between leaf paths (as we don't allow them), we might have hash collisions
/// between leaf paths and subpaths, so can't rely on `SubpathLookup` to only contain only one entry for the leaf path hash.
type PathLookup = HashMap<PathHash, LeafPathComponent>;

/// Used for optimal subpath reuse / deduplication and handling file / folder name collision errors.
/// Here the `PathHash` key is the accumulated hash of the entire subpath so far.
///
/// The subpath hash is obtained by hashing folder names and file names / file stems and extensions.
/// E.g. the path "foo/bar.txt" is hashed as a sequence of strings `[ "foo", "bar", "txt" ]`.
/// NOTE - this is different from the full file path hash used in `PathLookup`, which would be hashed as `[ "foo", "bar.txt" ]`.
type SubpathLookup = MultiMap<PathHash, SubpathComponent>;

/// Used for optimal path component (folder name, file name, file stem, extension) string reuse / deduplication.
/// Here the `PathHash` key is the hash of just a single path component string.
type StringLookup = MultiMap<PathHash, StringIndex>;

/// Array of all unique path components added so far for folder / file name / file stem subpaths (but not for extensions).
/// Index into by `PathLookup` and `SubpathLookup` entries.
type PathComponents = Vec<PathComponent>;

/// Array of all unique strings added so far.
/// Indexed into by `PathComponents` entries.
/// Used to index into the `String`.
type StringTable = Vec<InternedString>;

/// Used for optimal extension string reuse / deduplication.
/// Here the `PathHash` key is the hash of just a single extension string.
type ExtensionLookup = MultiMap<PathHash, ExtensionIndex>;

/// Array of all unique extensions added so far.
/// Indexed into by `ExtensionLookup` entries.
/// Used to index into the `StringTable`.
type ExtensionTable = Vec<StringIndex>;

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
    /// Persistent lookup map from a full file path hash to its leaf path component.
    /// See `PathLookup`.
    ///
    /// Needed by the writer and serialized to the data blob.
    path_lookup: PathLookup,
    /// Temporary lookup map from each valid subpath hash added so far to its index
    /// (or indices, if there's subpath string hash collisions) in the `path_components` array.
    /// See `SubpathLookup`.
    ///
    /// Needed only by the writer, not serialized to the data blob.
    subpath_lookup: SubpathLookup,
    /// Persistent array of valid path components added so far.
    /// Indexed into by entries of `subpath_lookup` and `path_lookup`.
    ///
    /// Needed by the writer and serialized to the data blob.
    path_components: PathComponents,
    /// Temporary lookup map from a single extension string's hash to its index
    /// (or indices, if there's subpath string hash collisions) in the `extension_table`.
    ///
    /// Needed only by the writer, not serialized to the data blob.
    extension_lookup: ExtensionLookup,
    /// Persistent array of unique extension string indices in the `string_table`.
    ///
    /// Needed by the writer and serialized to the data blob.
    extension_table: ExtensionTable,
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

impl<H> FileTreeWriter<H>
where
    H: BuildHasher,
    // TODO: `Clone` requirement might be relaxed, but it would require hashing path strings in parallel more than once,
    // bit I assume cloning any reasonable hasher is very cheap.
    H::Hasher: Clone,
{
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
            path_lookup: PathLookup::new(),
            subpath_lookup: SubpathLookup::new(),
            path_components: Vec::new(),
            extension_lookup: MultiMap::new(),
            extension_table: Vec::new(),
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

        // Count the number of components (needed to process the extension, if any, separately in the main loop below),
        // and hash the path fully to determine straight up if we have a path hash collision
        // (or the same path is being inserted more then once).
        // Need to preprocess to avoid inserting strings / subpaths into the lookup if the path is ultimately found to be invalid.
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
                debug_assert_eq!(
                    path_hash, _path_hash,
                    "path hashing assumes paths are hashed component-wise"
                );
            }

            (num_components, path_hash)
        };

        // Check for full file path hash collisions (or the same path added more than once).
        if let Some(&lpc) = self.path_lookup.get(&path_hash) {
            if self
                .iter(lpc.path_component, lpc.extension)
                .eq(file_path_rev_iter(path))
            {
                return Err(FileTreeWriterError::PathAlreadyExists);
            } else {
                return Err(FileTreeWriterError::PathHashCollision(self.path_buf(
                    lpc.path_component,
                    lpc.extension,
                    lpc.string_len,
                    //lpc.is_extension,
                )));
            }
        }

        // Explicitly handle file names with extensions which match folder names of the same form.
        //
        // E.g. we want to error out when first inserting "foo/bar.txt/baz" (folder name "bar.txt"),
        // then "foo/bar.txt" (file name "bar.txt").
        // Otherwise, code below will not match folder name "foo" followed by file stem "bar"
        // and will insert a new component and continue instead of returning an error.
        //
        // To do this, we hash the path as if its file name with extension was a folder name.
        //
        // Also see `folder_name_as_file_stem_and_extension_rev_iter()`.
        let mut subpath_hasher = self.hash_builder.build_hasher();

        for path_component in path_component_and_extension_iter(path, num_components) {
            match path_component {
                PathComponentKind::Folder(folder_name) => {
                    subpath_hasher.write(folder_name.as_bytes());
                }
                PathComponentKind::FileStem(file_stem) => {
                    subpath_hasher.write(file_stem_str(&file_stem).as_bytes());
                }
                PathComponentKind::Extension(extension) => {
                    // Re-hash the file name with an extension as a folder name
                    // (i.e., do `hash("foo", "bar.txt")` for path "foo/bar.txt" instead of the normal `hash("foo", "bar", "txt")`).
                    subpath_hasher.write(".".as_bytes());
                    subpath_hasher.write(extension.as_bytes());
                    let subpath_hash = subpath_hasher.finish();

                    for folder_spc in self
                        .subpath_lookup
                        .get_iter(&subpath_hash)
                        .cloned()
                        // Only look for folder name subpaths.
                        .filter(SubpathComponent::is_folder_name)
                    {
                        if self
                            .folder_name_as_file_stem_and_extension_rev_iter(
                                folder_spc.path_component_or_file_stem_index,
                            )
                            .eq(file_path_rev_iter(path))
                        {
                            return Err(FolderAlreadyExistsAtFilePath);
                        }
                    }
                }
                // File names with no extension have no such issue.
                PathComponentKind::FileName(_) => {}
            }
        }

        // See `SubpathHash`.
        let mut subpath_hasher = self.hash_builder.build_hasher();
        // This is used to hash folder names which alias file names with extensions.
        // See `find_file_name_with_extension_for_folder_name()` below.
        let mut folder_name_hasher = self.hash_builder.build_hasher();

        // Index of the parent path component for each processed path component in the loop below;
        // index of the leaf/file path component after the last one was processed.
        let mut parent_index = None;
        // If the file name has an extension, this will be its index in the extension table.
        let mut extension_index = None;
        // Full file path string length, separators included.
        let mut string_len: FullStringLength = 0;

        for path_component in path_component_and_extension_iter(path, num_components) {
            let path_component_str = path_component.as_str();

            string_len += path_component_str.len() as FullStringLength;

            // Hash the subpath string so far.
            debug_assert_eq!(subpath_hasher.finish(), folder_name_hasher.finish());
            subpath_hasher.write(path_component_str.as_bytes());
            let subpath_hash = subpath_hasher.finish();

            // Check if the path component / file tree node for this subpath already exists
            let subpath = Self::reuse_subpath(
                &mut self.subpath_lookup,
                &self.path_components,
                &self.extension_table,
                &self.string_table,
                &self.strings,
                subpath_hash,
                path_component.as_str(),
                parent_index,
            );

            let subpath = if let Some(subpath) = subpath {
                Some(subpath)
            } else {
                // Explicitly handle folder names which match file names with extensions of the same form.
                //
                // E.g. we want to error out when first inserting "foo/bar.txt" (file name with extension "bar.txt"),
                // then "foo/bar.txt/baz" (folder name "bar.txt").
                // Otherwise, code above will match folder name "foo", but not folder name "bar.txt",
                // and we will insert a new component (file stem "bar") and continue instead of returning an error.
                //
                // "foo/bar.txt/..." -> "foo/bar.txt/..." => "bar.txt" is a folder name, would be reused above
                // "foo/bar/txt" -> "foo/bar.txt/baz" => "txt" is a file name, no reuse happens.
                // "foo/bar/txt.cfg" -> "foo/bar.txt/baz" => "txt" is a file stem, no reuse happens.
                // "foo/bar.txt" -> "foo/bar.txt/baz" => "txt" is an extension, error.
                //
                // Also see `find_file_name_with_extension_for_folder_name()`.
                if let Some(subpath) = self.find_file_name_with_extension_for_folder_name(
                    folder_name_hasher.clone(),
                    path_component,
                    parent_index,
                ) {
                    debug_assert!(subpath.is_extension());

                    return Err(FileAlreadyExistsAtFolderPath(self.path_buf(
                        subpath.path_component_or_file_stem_index,
                        subpath.extension_index,
                        subpath.string_len,
                    )));
                }

                None
            };

            // Reset the folder name hasher to the current subpath hash.
            folder_name_hasher = subpath_hasher.clone();

            let subpath_index = if let Some(subpath) = subpath {
                match path_component {
                    PathComponentKind::FileName(_) => {
                        // Reused the (folder name, file stem or extension) subpath as the file name.

                        // First check if we reused a folder name as the file name, which is an error.
                        // E.g. reusing folder name "bar" in "foo/bar/baz.txt" as a file name in "foo/bar".
                        if subpath.is_folder_name() {
                            // Can use `subpath_hash` in `path_lookup` because the path has no extension.
                            debug_assert!(!self.path_lookup.contains_key(&subpath_hash));
                            return Err(FolderAlreadyExistsAtFilePath);
                        }

                        // Reused the (file stem or extension) subpath as the file name.
                        subpath.reuse_as_file_name();

                        // Reused an extension with no path component as the file name - need to add a path component for the extension
                        // and modify the subpath to use the new path component instead.
                        // Leaf path component for the subpath will still use the extension index.
                        if subpath.is_extension() {
                            // Extension subpath with an extension index - `path_component_or_file_stem_index` points to the file stem path component.
                            // Need to create an extension path component.
                            if subpath.extension_index.take().is_some() {
                                let extension_index = Self::add_component(
                                    &mut self.path_components,
                                    &mut self.string_lookup,
                                    &mut self.string_table,
                                    &mut self.strings,
                                    self.hash_builder.build_hasher(),
                                    path_component,
                                    parent_index,
                                );

                                subpath.path_component_or_file_stem_index = extension_index;

                                extension_index
                            } else {
                                // Extension subpath with no extension index - `path_component_or_file_stem_index` points to the extension path component.
                                subpath.path_component_or_file_stem_index
                            }
                        } else {
                            // Reused the file stem subpath as file name.
                            subpath.path_component_or_file_stem_index
                        }
                    }
                    PathComponentKind::Folder(_) => {
                        // Reused (any) subpath as folder name.

                        // First check if we reused a file name as a folder name, which is an error.
                        // E.g. reusing file name "bar" in "foo/bar" as a folder name in "foo/bar/baz.txt".
                        if subpath.is_file_name() {
                            let index = subpath.path_component_or_file_stem_index;
                            let extension_index = subpath.extension_index;
                            let string_len = subpath.string_len;

                            return Err(FileAlreadyExistsAtFolderPath(self.path_buf(
                                index,
                                extension_index,
                                string_len,
                            )));
                        }

                        // Reused the (folder name, file stem or extension) subpath as folder name.
                        subpath.reuse_as_folder_name();

                        // Reused an extension with no path component as the folder name - need to add a path component for the extension
                        // and modify the subpath to use the new path component instead.
                        if subpath.is_extension() {
                            if subpath.extension_index.take().is_some() {
                                // Extension subpath with an extension index - `path_component_or_file_stem_index` points to the file stem path component.
                                // Need to create an extension path component.
                                let extension_index = Self::add_component(
                                    &mut self.path_components,
                                    &mut self.string_lookup,
                                    &mut self.string_table,
                                    &mut self.strings,
                                    self.hash_builder.build_hasher(),
                                    path_component,
                                    parent_index,
                                );

                                subpath.path_component_or_file_stem_index = extension_index;

                                extension_index
                            } else {
                                // Extension subpath with no extension index - `path_component_or_file_stem_index` points to the extension path component.
                                subpath.path_component_or_file_stem_index
                            }
                        } else {
                            // Reused the folder name or file stem subpath as folder name.
                            subpath.path_component_or_file_stem_index
                        }
                    }
                    PathComponentKind::FileStem(_) => {
                        // Reused (any) subpath as file stem.
                        subpath.reuse_as_file_stem();

                        // Reused an extension with no path component as the file stem - need to add a path component for the extension
                        // and modify the subpath to use the new path component instead.
                        if subpath.is_extension() {
                            if subpath.extension_index.take().is_some() {
                                // Extension subpath with an extension index - `path_component_or_file_stem_index` points to the file stem path component.
                                // Need to create an extension path component.
                                let extension_index = Self::add_component(
                                    &mut self.path_components,
                                    &mut self.string_lookup,
                                    &mut self.string_table,
                                    &mut self.strings,
                                    self.hash_builder.build_hasher(),
                                    path_component,
                                    parent_index,
                                );

                                subpath.path_component_or_file_stem_index = extension_index;

                                extension_index
                            } else {
                                // Extension subpath with no extension index - `path_component_or_file_stem_index` points to the extension path component.
                                subpath.path_component_or_file_stem_index
                            }
                        // Reused the (file name, folder name or file stem) subpath as folder name.
                        } else {
                            subpath.path_component_or_file_stem_index
                        }
                    }
                    PathComponentKind::Extension(extension) => {
                        // Reused a (folder name, file name or file stem) subpath as extension.
                        subpath.reuse_as_extension();

                        // Reuse an existing extension, or add a new one.
                        // Always add a new extension and make the leaf path component use it, even if we could use the reused path component for this purpose.
                        // This reuse is rare, and always requiring leaf path components for file names with extensions
                        // to have an extension index makes them more compact and simplifies the logic.
                        let extension_index_ = Self::extension_index(
                            &mut self.string_lookup,
                            &mut self.string_table,
                            &mut self.strings,
                            &mut self.extension_lookup,
                            &mut self.extension_table,
                            extension,
                            &self.hash_builder,
                        );

                        extension_index.replace(extension_index_);

                        // Must succeed - extension path components must have a file stem parent path component.
                        unsafe { debug_unwrap(parent_index) }
                    }
                }
            // We have not reused the current subpath.
            } else {
                // We are processing an extension - try to reuse an existing extension, or add a new one.
                if let PathComponentKind::Extension(extension) = path_component {
                    let extension_index_ = Self::extension_index(
                        &mut self.string_lookup,
                        &mut self.string_table,
                        &mut self.strings,
                        &mut self.extension_lookup,
                        &mut self.extension_table,
                        extension,
                        &self.hash_builder,
                    );

                    extension_index.replace(extension_index_);

                    // Must succeed - extension path components must have a file stem parent path component.
                    let file_stem_index = unsafe { debug_unwrap(parent_index) };

                    self.subpath_lookup.insert(
                        subpath_hash,
                        SubpathComponent::new_extension(
                            file_stem_index,
                            extension_index_,
                            string_len,
                        ),
                    );

                    file_stem_index

                // We are processing a folder name, file name or file stem component - add a new path component for it.
                } else {
                    let path_component_index = Self::add_component(
                        &mut self.path_components,
                        &mut self.string_lookup,
                        &mut self.string_table,
                        &mut self.strings,
                        self.hash_builder.build_hasher(),
                        path_component,
                        parent_index,
                    );

                    self.subpath_lookup.insert(
                        subpath_hash,
                        match path_component {
                            PathComponentKind::Folder(_) => {
                                SubpathComponent::new_folder(path_component_index, string_len)
                            }
                            PathComponentKind::FileName(_) => {
                                SubpathComponent::new_file_name(path_component_index, string_len)
                            }
                            PathComponentKind::FileStem(_) => {
                                SubpathComponent::new_file_stem(path_component_index, string_len)
                            }
                            PathComponentKind::Extension(_) => {
                                // Extensions are handled above.
                                debug_unreachable()
                            }
                        },
                    );

                    path_component_index
                }
            };

            // Update the parent index to the current path component index.
            parent_index.replace(subpath_index);

            // Account for the path component separator in the total string length.
            if !matches!(
                path_component,
                PathComponentKind::Extension(_) | PathComponentKind::FileName(_)
            ) {
                string_len += 1;
            }
        }

        // Update the leaf path components.

        // Must succeed if we got here, or we'd error out above.
        let parent_index = unsafe { debug_unwrap(parent_index) };

        let _none = self.path_lookup.insert(
            path_hash,
            LeafPathComponent::new(parent_index, extension_index, string_len),
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
            self.extension_table.len() as _,
            version,
        );

        written += header.write(w)?;

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Path lookup.

        // Get and sort the path hashes.
        // NOTE - sorting is relied upon for binary search in `FileTreeReader::lookup_leaf_path_component()`.
        let mut path_hashes = self.path_lookup.keys().cloned().collect::<Vec<_>>();
        path_hashes.sort();

        // Write the path hashes.
        for &path_hash in path_hashes.iter() {
            written += write_u64(w, path_hash)?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Write the leaf path components.
        for lpc in path_hashes
            .iter()
            // Must succeed - all keys are contained in the map.
            .map(|path_hash| *unsafe { debug_unwrap(self.path_lookup.get(path_hash)) })
        {
            written += lpc.write(w)?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Write the path components array.
        for path_component in self.path_components {
            written += path_component.write(w)?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Write the extension table.
        for extension in self.extension_table {
            written += write_u32(w, extension)?;
        }

        // Align to 8 bytes.
        let mut to_write = written % 8;
        while to_write > 0 {
            w.write_all(&[b'0'])?;
            written += 1;
            to_write -= 1;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Write the string table.
        // Patch up the string offsets to be relative to the start of the blob.
        let string_offset =
            (written + self.string_table.len() * size_of::<PackedInternedString>()) as StringOffset;

        for string in self.string_table.iter() {
            written += string.write(w, string_offset)?;
        }

        debug_assert!(written % 8 == 0, "should be aligned to 8 bytes");

        // Write the strings.
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
    pub fn string_len(&self) -> u64 {
        self.strings.len() as u64
    }

    /// Returns the number of unique path components [`inserted`](#method.insert) into the writer.
    pub fn num_components(&self) -> usize {
        self.path_components.len()
    }

    /// Returns the number of unique extensions [`inserted`](#method.insert) into the writer.
    pub fn num_extensions(&self) -> usize {
        self.extension_table.len()
    }

    #[cfg(test)]
    fn num_subpaths(&self) -> usize {
        self.subpath_lookup.values().count()
    }

    /// Clears the writer, resetting all internal data structures without deallocating any storage.
    pub fn clear(&mut self) {
        self.subpath_lookup.clear();
        self.string_lookup.clear();
        self.path_lookup.clear();
        self.path_components.clear();
        self.extension_lookup.clear();
        self.extension_table.clear();
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
            Ok(self.build_path_string(lpc.path_component, lpc.extension, lpc.string_len, builder))
        } else {
            Err(builder)
        }
    }

    /// Returns the [`file path`](FilePathBuf) associated with the file path `hash`, if any.
    pub fn lookup(&self, hash: PathHash) -> Option<FilePathBuf> {
        self.lookup_into(hash, FilePathBuilder::new()).ok()
    }

    #[cfg(test)]
    fn lookup_iter(
        &self,
        hash: PathHash,
    ) -> Option<FilePathIter<'_, impl Iterator<Item = FilePathComponent<'_>>>> {
        self.path_lookup
            .get(&hash)
            .map(|lpc| self.iter(lpc.path_component, lpc.extension))
    }

    /// Returns a (reverse) file path iterator for the path component at `index` with an optional `extension_index`.
    /// The caller guarantees the path component `index` and `extension_index`, if any, are valid.
    fn iter(
        &self,
        index: PathComponentIndex,
        extension_index: Option<ExtensionIndex>,
    ) -> FilePathIter<'_, impl Iterator<Item = FilePathComponent<'_>>> {
        let path_component = get_path_component(&self.path_components, index);

        // If `extension_index` is `Some`, `path_component` is for the file stem.
        let file_name = if let Some(extension_index) = extension_index {
            // Extensions may not be empty.
            let extension = get_non_empty_string(
                &self.string_table,
                &self.strings,
                get_extension(&self.extension_table, extension_index),
            );
            // File stems may be empty.
            let file_stem = NonEmptyStr::new(get_string(
                &self.string_table,
                &self.strings,
                path_component.string,
            ));

            FileName::WithExtension {
                extension,
                file_stem,
            }
        } else {
            // File names (with no extension) may not be empty.
            FileName::NoExtension(get_non_empty_string(
                &self.string_table,
                &self.strings,
                path_component.string,
            ))
        };

        FilePathIter {
            file_name,
            file_path: FolderIter::new(
                &self.path_components,
                &self.extension_table,
                &self.string_table,
                &self.strings,
                path_component.parent,
            ),
        }
    }

    /// Returns a (reverse) file path iterator for the folder path component at `index`,
    /// treating the folder name as a potential file name with an extension.
    ///
    /// E.g. if `index` points to folder "bar.txt" in "foo/bar.txt/...", this will return an iterator
    /// treating "bar.txt" as a file stem with extension, to match an actual inserted file name with extension like "foo/bar.txt".
    fn folder_name_as_file_stem_and_extension_rev_iter(
        &self,
        index: PathComponentIndex,
    ) -> FilePathIter<'_, impl Iterator<Item = FilePathComponent<'_>>> {
        let path_component = get_path_component(&self.path_components, index);

        // Folder names may not be empty.
        let folder_name =
            get_non_empty_string(&self.string_table, &self.strings, path_component.string);

        let file_name = if let Some(FileStemAndExtension {
            file_stem,
            extension,
        }) = file_stem_and_extension(folder_name)
        {
            FileName::WithExtension {
                extension,
                file_stem,
            }
        } else {
            FileName::NoExtension(folder_name)
        };

        FilePathIter {
            file_name,
            file_path: FolderIter::new(
                &self.path_components,
                &self.extension_table,
                &self.string_table,
                &self.strings,
                path_component.parent,
            ),
        }
    }

    /// If `path_component` is a folder name with a dot in it, returns an existing subpath, if any,
    /// for a file name with an extension which matches the string of the subpath for `path_component` with `parent_index`.
    ///
    /// E.g., this will return "foo/bar.txt" for folder name `path_component` "bar.txt" if we are inserting "foo/bar.txt/...".
    fn find_file_name_with_extension_for_folder_name(
        &self,
        mut folder_name_hasher: H::Hasher,
        path_component: PathComponentKind<'_>,
        parent_index: Option<PathComponentIndex>,
    ) -> Option<SubpathComponent> {
        if let PathComponentKind::Folder(folder_name) = path_component {
            file_stem_and_extension(folder_name).and_then(
                |FileStemAndExtension {
                     file_stem,
                     extension,
                 }| {
                    // Hash the folder name as if it were a file name with an extension (i.e. skip the dot. See `SubpathLookup`).
                    folder_name_hasher.write(file_stem_str(&file_stem).as_bytes());
                    folder_name_hasher.write(extension.as_bytes());
                    let folder_name_hash = folder_name_hasher.finish();

                    self.subpath_lookup
                        .get_iter(&folder_name_hash)
                        .cloned()
                        // Only look for extension subpaths.
                        .filter(SubpathComponent::is_extension)
                        .find(|extension_spc| {
                            let exising_subpath = Self::string_rev_iter(
                                &self.path_components,
                                &self.extension_table,
                                &self.string_table,
                                &self.strings,
                                extension_spc.path_component_or_file_stem_index,
                                extension_spc.extension_index,
                            );
                            let new_subpath = iter::once(extension.as_str())
                                .chain(iter::once(file_stem_str(&file_stem)))
                                .chain(StringIter::new(
                                    &self.path_components,
                                    &self.extension_table,
                                    &self.string_table,
                                    &self.strings,
                                    parent_index,
                                    None,
                                ));

                            new_subpath.eq(exising_subpath)
                        })
                },
            )
        } else {
            None
        }
    }

    /// Returns a (reverse) iterator over path component strings
    /// (i.e. folder names, file names, (maybe empty) file stems and extensions)
    /// for the path component at `index`.
    ///
    /// The caller guarantees the path component `index` is valid.
    fn string_rev_iter<'a>(
        path_components: &'a [PathComponent],
        extension_table: &'a [StringIndex],
        string_table: &'a [InternedString],
        strings: &'a String,
        index: PathComponentIndex,
        extension_index: Option<ExtensionIndex>,
    ) -> impl Iterator<Item = &'a str> {
        StringIter::new(
            path_components,
            extension_table,
            string_table,
            strings,
            Some(index),
            extension_index,
        )
    }

    /// Attempts to find an existing subpath (i.e. a linked list of strings)
    /// matching the `path_component`, `subpath_hash` and `parent_index`.
    ///
    /// The caller guarantees `subpath_hash` is the subpath hash for `path_component` (see `SubpathLookup`),
    /// and that `parent_index`, if any, is valid.
    fn reuse_subpath<'a>(
        subpath_lookup: &'a mut SubpathLookup,
        path_components: &[PathComponent],
        extension_table: &[StringIndex],
        string_table: &[InternedString],
        strings: &String,
        subpath_hash: PathHash,
        path_component: &str,
        parent_index: Option<PathComponentIndex>,
    ) -> Option<&'a mut SubpathComponent> {
        subpath_lookup.get_iter_mut(&subpath_hash).find(|spc| {
            let existing_subpath = Self::string_rev_iter(
                path_components,
                extension_table,
                string_table,
                strings,
                spc.path_component_or_file_stem_index,
                spc.extension_index,
            );
            let new_subpath = iter::once(path_component).chain(StringIter::new(
                path_components,
                extension_table,
                string_table,
                strings,
                parent_index,
                None,
            ));

            new_subpath.eq(existing_subpath)
        })
    }

    /// Adds the new unique `path_component` with `parent_index` parent (if any) to the lookup structures.
    fn add_component(
        path_components: &mut PathComponents,
        string_lookup: &mut StringLookup,
        string_table: &mut StringTable,
        strings: &mut String,
        hasher: H::Hasher,
        path_component: PathComponentKind,
        parent_index: Option<PathComponentIndex>,
    ) -> PathComponentIndex {
        // Add the new path component to the lookup array, using the current parent index, if any.
        let path_component_ =
            // Get / intern the path component's string index in the string table.
            PathComponent::new(
                Self::string_index(
                    string_lookup,
                    string_table,
                    strings,
                    path_component.as_str(),
                    hasher,
                ),
                parent_index
            );

        // All path components must be unique.
        #[cfg(debug_assertions)]
        {
            debug_assert!(!path_components.iter().any(|pc| *pc == path_component_));
        }

        let path_component_index = path_components.len() as PathComponentIndex;
        path_components.push(path_component_);

        path_component_index
    }

    /// Returns the index of the existing `extension` in the extension table, if it exists,
    /// or adds it and returns its new index in the extension table.
    fn extension_index(
        string_lookup: &mut StringLookup,
        string_table: &mut StringTable,
        strings: &mut String,
        extension_lookup: &mut ExtensionLookup,
        extension_table: &mut ExtensionTable,
        extension: FilePathComponent<'_>,
        hash_builder: &H,
    ) -> ExtensionIndex {
        let extension_hash = {
            let mut hasher = hash_builder.build_hasher();
            hasher.write(extension.as_bytes());
            hasher.finish()
        };

        if let Some(extension_index) = extension_lookup
            // First lookup by string hash.
            .get_iter(&extension_hash)
            // Then compare the strings.
            .find(|&&extension_index| {
                get_string(
                    string_table,
                    strings,
                    get_extension(extension_table, extension_index),
                ) == extension.as_str()
            })
        {
            // If the extension already exists - return its index.
            return *extension_index;
        }

        // Else the extension does not exist - intern its string, add it and return its index.
        let extension_string_index = Self::string_index_with_hash(
            string_lookup,
            string_table,
            strings,
            extension.as_str(),
            extension_hash,
        );
        let extension_index = extension_table.len() as ExtensionIndex;
        extension_table.push(extension_string_index);
        extension_lookup.insert(extension_hash, extension_index);
        extension_index
    }

    /// Used for error reporting.
    /// The caller guarantees the path component `index` and the `extension_index`, if any, are valid.
    fn path_buf(
        &self,
        index: PathComponentIndex,
        extension_index: Option<ExtensionIndex>,
        string_len: FullStringLength,
    ) -> FilePathBuf {
        self.build_path_string(index, extension_index, string_len, FilePathBuilder::new())
    }

    /// The caller guarantees the path component `index` and the `extension_index`, if any, are valid,
    /// and that `string_len` matches the actual string length.
    fn build_path_string(
        &self,
        index: PathComponentIndex,
        extension_index: Option<ExtensionIndex>,
        string_len: FullStringLength,
        builder: FilePathBuilder,
    ) -> FilePathBuf {
        let mut string = builder.into_inner();
        build_path_string(self.iter(index, extension_index), string_len, &mut string);
        debug_assert!(!string.is_empty());
        unsafe { FilePathBuf::new_unchecked(string) }
    }

    /// Returns the string index of the interned `string` in the string table, if it is interned,
    /// or interns it and returns its new index in the string table.
    fn string_index(
        string_lookup: &mut StringLookup,
        string_table: &mut StringTable,
        strings: &mut String,
        string: &str,
        mut hasher: H::Hasher,
    ) -> StringIndex {
        // First hash the path component's string and check if was already added.
        hasher.write(string.as_bytes());
        let string_hash = hasher.finish();

        Self::string_index_with_hash(string_lookup, string_table, strings, string, string_hash)
    }

    /// Returns the string index of the interned `string` with `hash` in the string table, if it is interned,
    /// or interns it and returns its new index in the string table.
    ///
    /// The caller guarantees `hash` is actually the `string`'s hash.
    fn string_index_with_hash(
        string_lookup: &mut StringLookup,
        string_table: &mut StringTable,
        strings: &mut String,
        string: &str,
        hash: PathHash,
    ) -> StringIndex {
        if let Some(string_index) = string_lookup
            // First lookup by string hash.
            .get_iter(&hash)
            // Then compare the strings.
            .find(|&&string_index| get_string(string_table, strings, string_index) == string)
        {
            // If the `string` already exists - return its index.
            return *string_index;
        }

        // Else the string does not exist - intern it and return its index.
        Self::intern_string(string_lookup, string_table, strings, string, hash)
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
fn get_path_component(
    path_components: &[PathComponent],
    index: PathComponentIndex,
) -> PathComponent {
    debug_assert!((index as usize) < path_components.len());
    *unsafe { path_components.get_unchecked(index as usize) }
}

/// The caller guarantees the extension `index` is valid.
fn get_extension(extension_table: &[StringIndex], index: ExtensionIndex) -> StringIndex {
    debug_assert!((index as usize) < extension_table.len());
    *unsafe { extension_table.get_unchecked(index as usize) }
}

/// The caller guarantees the string `index` is valid.
fn get_string<'s>(
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
fn get_non_empty_string<'s>(
    string_table: &[InternedString],
    strings: &'s String,
    index: StringIndex,
) -> &'s NonEmptyStr {
    let string = get_string(string_table, strings, index);
    debug_assert!(!string.is_empty());
    unsafe { NonEmptyStr::new_unchecked(string) }
}

/// Returns a (reverse) file path iterator over the components of `path`.
fn file_path_rev_iter(
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

bitflags! {
    /// Need to disambiguate between subpath components of different types to reuse them when possible,
    /// and to handle `FolderAlreadyExistsAtFilePath` / `FileAlreadyExistsAtFolderPath` errors.
    struct SubpathFlags: u8 {
        const Extension = 0b0001;
        const FileStem = 0b0010;
        const FileName = 0b0100;
        const FolderName = 0b1000;
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct SubpathComponent {
    path_component_or_file_stem_index: PathComponentIndex,
    extension_index: Option<ExtensionIndex>,
    string_len: FullStringLength,
    flags: SubpathFlags,
}

impl SubpathComponent {
    fn new_folder(path_component: PathComponentIndex, string_len: FullStringLength) -> Self {
        Self {
            path_component_or_file_stem_index: path_component,
            extension_index: None,
            string_len,
            flags: SubpathFlags::FolderName,
        }
    }

    fn new_file_name(path_component: PathComponentIndex, string_len: FullStringLength) -> Self {
        Self {
            path_component_or_file_stem_index: path_component,
            extension_index: None,
            string_len,
            flags: SubpathFlags::FileName,
        }
    }

    fn new_file_stem(path_component: PathComponentIndex, string_len: FullStringLength) -> Self {
        Self {
            path_component_or_file_stem_index: path_component,
            extension_index: None,
            string_len,
            flags: SubpathFlags::FileStem,
        }
    }

    fn new_extension(
        file_stem: PathComponentIndex,
        extension: ExtensionIndex,
        string_len: FullStringLength,
    ) -> Self {
        Self {
            path_component_or_file_stem_index: file_stem,
            extension_index: Some(extension),
            string_len,
            flags: SubpathFlags::Extension,
        }
    }

    fn is_folder_name(&self) -> bool {
        self.flags.contains(SubpathFlags::FolderName)
    }

    fn is_file_name(&self) -> bool {
        self.flags.contains(SubpathFlags::FileName)
    }

    fn is_extension(&self) -> bool {
        self.flags.contains(SubpathFlags::Extension)
    }

    // File stem or extension subpaths can be reused as file names.
    fn reuse_as_file_name(&mut self) {
        debug_assert!(!self.flags.contains(SubpathFlags::FileName));
        debug_assert!(!self.flags.contains(SubpathFlags::FolderName));
        debug_assert!(
            self.flags.contains(SubpathFlags::FileStem)
                || self.flags.contains(SubpathFlags::Extension)
        );
        self.flags.set(SubpathFlags::FileName, true);
    }

    // Folder name, file stem or extension subpaths can be reused as folder names.
    fn reuse_as_folder_name(&mut self) {
        debug_assert!(!self.flags.contains(SubpathFlags::FileName));
        debug_assert!(
            self.flags.contains(SubpathFlags::FolderName)
                || self.flags.contains(SubpathFlags::FileStem)
                || self.flags.contains(SubpathFlags::Extension)
        );
        self.flags.set(SubpathFlags::FolderName, true);
    }

    // Any component type may be reused as a file stem.
    fn reuse_as_file_stem(&mut self) {
        self.flags.set(SubpathFlags::FileStem, true);
    }

    // Folder name, file name or file stem subpaths can be reused as extensions.
    fn reuse_as_extension(&mut self) {
        debug_assert!(!self.flags.contains(SubpathFlags::Extension));
        debug_assert!(
            self.flags.contains(SubpathFlags::FolderName)
                || self.flags.contains(SubpathFlags::FileName)
                || self.flags.contains(SubpathFlags::FileStem)
        );
        debug_assert!(self.extension_index.is_none());
        self.flags.set(SubpathFlags::Extension, true);
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PathComponentKind<'a> {
    Folder(FilePathComponent<'a>),
    FileName(FilePathComponent<'a>),
    FileStem(Option<FilePathComponent<'a>>),
    Extension(FilePathComponent<'a>),
}

impl<'a> PathComponentKind<'a> {
    fn as_str(&self) -> &str {
        match self {
            PathComponentKind::Folder(folder) => folder.as_str(),
            PathComponentKind::FileName(file_name) => file_name.as_str(),
            PathComponentKind::FileStem(file_stem) => file_stem_str(file_stem),
            PathComponentKind::Extension(extension) => extension.as_str(),
        }
    }
}

/// (Forward) iterator over folder names and file name / file stem and extension of the file `path`.
/// Needs `num_components` to know when processing the last component of the file path and check for extension.
struct PathComponentAndExtensionIter<'a, T> {
    num_components: NumComponents,
    extension: Option<FilePathComponent<'a>>,
    components: T,
}

impl<'a, T> PathComponentAndExtensionIter<'a, T> {
    fn new(components: T, num_components: NumComponents) -> Self {
        Self {
            num_components,
            extension: None,
            components,
        }
    }
}

impl<'a, T> Iterator for PathComponentAndExtensionIter<'a, T>
where
    T: Iterator<Item = FilePathComponent<'a>>,
{
    type Item = PathComponentKind<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(extension) = self.extension.take() {
            debug_assert_eq!(self.num_components, 0);
            Some(PathComponentKind::Extension(extension))
        } else if self.num_components > 1 {
            self.num_components -= 1;
            self.components.next().map(PathComponentKind::Folder)
        } else if self.num_components == 1 {
            self.num_components -= 1;
            self.components.next().map(|file_name| {
                if let Some(FileStemAndExtension {
                    file_stem,
                    extension,
                }) = file_stem_and_extension(file_name)
                {
                    self.extension.replace(extension);
                    PathComponentKind::FileStem(file_stem)
                } else {
                    PathComponentKind::FileName(file_name)
                }
            })
        } else {
            None
        }
    }
}

/// Returns a (forward) iterator over folder names and file name / file stem and extension of the file `path` with `num_components`.
///
/// E.g., for `"foo/bar/baz.txt"`, this will return `[Folder("foo"), Folder("bar"), FileStem("baz"), Extension("txt")]`;
/// for `"foo/bar/baz"`, this will return `[Folder("foo"), Folder("bar"), FileName("baz")]`.
///
/// The caller guarantees `path` actually has `num_components`.
fn path_component_and_extension_iter(
    path: &FilePath,
    num_components: NumComponents,
) -> impl Iterator<Item = PathComponentKind<'_>> {
    PathComponentAndExtensionIter::new(path.components(), num_components)
}

/// (Reverse) iterator over strings of file path components starting at `index`, if any
/// (i.e. folder names, file names, (maybe empty) file stems and extensions).
struct StringIter<'a> {
    path_components: &'a [PathComponent],
    extension_table: &'a [StringIndex],
    string_table: &'a [InternedString],
    strings: &'a String,
    index: Option<PathComponentIndex>,
    extension_index: Option<ExtensionIndex>,
}

impl<'a> StringIter<'a> {
    /// The caller guarantees the path component `index` and `extension_index`, if any, are valid.
    fn new(
        path_components: &'a [PathComponent],
        extension_table: &'a [StringIndex],
        string_table: &'a [InternedString],
        strings: &'a String,
        index: Option<PathComponentIndex>,
        extension_index: Option<ExtensionIndex>,
    ) -> Self {
        Self {
            path_components,
            extension_table,
            string_table,
            strings,
            index,
            extension_index,
        }
    }
}

impl<'a> Iterator for StringIter<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(extension_index) = self.extension_index.take() {
            let extension_string_index = get_extension(self.extension_table, extension_index);
            Some(get_string(
                self.string_table,
                self.strings,
                extension_string_index,
            ))
        } else {
            self.index.take().map(|index| {
                let path_component = get_path_component(self.path_components, index);
                if let Some(parent) = path_component.parent {
                    self.index.replace(parent);
                }
                get_string(self.string_table, self.strings, path_component.string)
            })
        }
    }
}

/// (Reverse) iterator over the (folder) file path components starting at some path component index.
struct FolderIter<'a>(StringIter<'a>);

impl<'a> FolderIter<'a> {
    fn new(
        path_components: &'a [PathComponent],
        extension_table: &'a [StringIndex],
        string_table: &'a [InternedString],
        strings: &'a String,
        index: Option<PathComponentIndex>,
    ) -> Self {
        Self(StringIter::new(
            path_components,
            extension_table,
            string_table,
            strings,
            index,
            None,
        ))
    }
}

impl<'a> Iterator for FolderIter<'a> {
    type Item = FilePathComponent<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|s| {
            // Folder names may not be empty.
            debug_assert!(!s.is_empty());
            unsafe { NonEmptyStr::new_unchecked(s) }
        })
    }
}

fn file_stem_str<'a>(file_stem: &'a Option<FilePathComponent<'_>>) -> &'a str {
    file_stem.map(NonEmptyStr::as_str).unwrap_or("")
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use {super::*, minifilepath_macro::filepath, ministr_macro::nestr, seahash::SeaHasher};

    #[test]
    fn path_component_and_extension_iter_test() {
        assert!(
            path_component_and_extension_iter(filepath!("foo/bar"), 2).eq(vec![
                PathComponentKind::Folder(nestr!("foo")),
                PathComponentKind::FileName(nestr!("bar"))
            ]
            .into_iter())
        );
        assert!(
            path_component_and_extension_iter(filepath!("foo/bar.txt"), 2).eq(vec![
                PathComponentKind::Folder(nestr!("foo")),
                PathComponentKind::FileStem(Some(nestr!("bar"))),
                PathComponentKind::Extension(nestr!("txt")),
            ]
            .into_iter())
        );
        assert!(
            path_component_and_extension_iter(filepath!("foo/bar/.txt"), 3).eq(vec![
                PathComponentKind::Folder(nestr!("foo")),
                PathComponentKind::Folder(nestr!("bar")),
                PathComponentKind::FileStem(None),
                PathComponentKind::Extension(nestr!("txt")),
            ]
            .into_iter())
        );
    }

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
            assert_eq!(
                writer.insert(filepath!("foo/bar")).err().unwrap(),
                FileTreeWriterError::FileAlreadyExistsAtFolderPath(filepath!("foo").into())
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar")).unwrap();
            assert_eq!(
                writer.insert(filepath!("foo/bar/baz")).err().unwrap(),
                FileTreeWriterError::FileAlreadyExistsAtFolderPath(filepath!("foo/bar").into())
            );
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar.txt")).unwrap();
            assert_eq!(
                writer.insert(filepath!("foo/bar.txt/baz")).err().unwrap(),
                FileTreeWriterError::FileAlreadyExistsAtFolderPath(filepath!("foo/bar.txt").into())
            );
        }

        // But this works.
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar.txt/baz")).unwrap();
            writer.insert(filepath!("foo/bar.txt/bob")).unwrap();
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar/txt")).unwrap();
            writer.insert(filepath!("foo/bar.txt/baz")).unwrap();
        }
        {
            let mut writer = FileTreeWriter::new(BuildSeaHasher::default());
            writer.insert(filepath!("foo/bar/txt.cfg")).unwrap();
            writer.insert(filepath!("foo/bar.txt/baz")).unwrap();
        }
    }

    #[derive(Clone, Copy)]
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

            #[derive(Clone, Copy)]
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

    #[test]
    fn reuse_file_name_as_file_name() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        {
            // Reuse file name "bar" as file name -> cannot happen, handled earlier by `PathAlreadyExists`

            // subpaths: [ hash("foo"), hash("foo", "bar") ]
            // bar: `SubpathFlags::FileOrFolderName`
            let bar = writer.insert(filepath!("foo/bar")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 2);
            assert_eq!(writer.num_extensions(), 0);
            assert_eq!(writer.string_len(), 6);
            assert_eq!(writer.lookup(bar).unwrap(), filepath!("foo/bar").into());
            {
                let bar = writer.lookup_iter(bar).unwrap();
                assert_eq!(bar.file_name, FileName::NoExtension(nestr!("bar")));
                assert!(bar.file_path.eq(vec![nestr!("foo")].into_iter()));
            }
            assert_eq!(
                writer.insert(filepath!("foo/bar")).err().unwrap(),
                FileTreeWriterError::PathAlreadyExists
            );

            writer.clear();
        }

        {
            // Reuse file name "txt" as file name -> cannot happen, handled earlier by `PathAlreadyExists`

            // subpaths: [ hash("foo.bar"), hash("foo.bar", "txt") ]
            // bar: `SubpathFlags::FileOrFolderName`
            let txt = writer.insert(filepath!("foo.bar/txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 2);
            assert_eq!(writer.num_extensions(), 0);
            assert_eq!(writer.string_len(), 10);
            assert_eq!(writer.lookup(txt).unwrap(), filepath!("foo.bar/txt").into());
            {
                let txt = writer.lookup_iter(txt).unwrap();
                assert_eq!(txt.file_name, FileName::NoExtension(nestr!("txt")));
                assert!(txt.file_path.eq(vec![nestr!("foo.bar")].into_iter()));
            }
            assert_eq!(
                writer.insert(filepath!("foo.bar/txt")).err().unwrap(),
                FileTreeWriterError::PathAlreadyExists
            );

            writer.clear();
        }
    }

    #[test]
    fn reuse_folder_name_as_file_name() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        {
            // Reuse folder name "bar" as file name -> `FolderAlreadyExistsAtFilePath`

            // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
            // bar: `SubpathFlags::FileOrFolderName`
            let txt = writer.insert(filepath!("foo/bar/txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 3);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 0);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(writer.lookup(txt).unwrap(), filepath!("foo/bar/txt").into());
            {
                let txt = writer.lookup_iter(txt).unwrap();
                assert_eq!(txt.file_name, FileName::NoExtension(nestr!("txt")));
                assert!(txt
                    .file_path
                    .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
            }
            assert_eq!(
                writer.insert(filepath!("foo/bar")).err().unwrap(),
                FileTreeWriterError::FolderAlreadyExistsAtFilePath
            );

            writer.clear();
        }

        {
            // Reuse folder name "bar.txt" as file name -> `FolderAlreadyExistsAtFilePath`

            // subpaths: [ hash("foo"), hash("foo", "bar.txt"), hash("foo", "bar.txt", baz") ]
            // bar: `SubpathFlags::FileOrFolderName`
            let baz = writer.insert(filepath!("foo/bar.txt/baz")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 3);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 0);
            assert_eq!(writer.string_len(), 13);
            assert_eq!(
                writer.lookup(baz).unwrap(),
                filepath!("foo/bar.txt/baz").into()
            );
            {
                let cfg = writer.lookup_iter(baz).unwrap();
                assert_eq!(cfg.file_name, FileName::NoExtension(nestr!("baz")));
                assert!(cfg
                    .file_path
                    .eq(vec![nestr!("bar.txt"), nestr!("foo")].into_iter()));
            }
            assert_eq!(
                writer.insert(filepath!("foo/bar.txt")).err().unwrap(),
                FileTreeWriterError::FolderAlreadyExistsAtFilePath
            );

            writer.clear();
        }
    }

    #[test]
    fn reuse_file_stem_as_file_name() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        // Reuse file stem "bar" as file name.

        // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
        // bar: `SubpathFlags::FileStem`
        let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
        assert_eq!(writer.len(), 1);
        assert_eq!(writer.num_components(), 2);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 1);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(
            writer.lookup(bar_txt).unwrap(),
            filepath!("foo/bar.txt").into()
        );
        {
            let bar_txt = writer.lookup_iter(bar_txt).unwrap();
            assert_eq!(
                bar_txt.file_name,
                FileName::WithExtension {
                    extension: nestr!("txt"),
                    file_stem: Some(nestr!("bar"))
                }
            );
            assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
        }

        // bar |= `SubpathFlags::FileOrFolderName`
        let bar = writer.insert(filepath!("foo/bar")).unwrap();
        assert_eq!(writer.len(), 2);
        assert_eq!(writer.num_components(), 2);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 1);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(writer.lookup(bar).unwrap(), filepath!("foo/bar").into());
        {
            let bar = writer.lookup_iter(bar).unwrap();
            assert_eq!(bar.file_name, FileName::NoExtension(nestr!("bar")));
            assert!(bar.file_path.eq(vec![nestr!("foo")].into_iter()));
        }
    }

    #[test]
    fn reuse_extension_as_file_name() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        {
            // Reuse extension "bar" as file name.

            // subpaths: [ hash("foo"), hash("foo", "bar") ]
            // bar: `SubpathFlags::Extension`
            let foo_bar = writer.insert(filepath!("foo.bar")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 1);
            assert_eq!(writer.num_subpaths(), 2);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 6);
            assert_eq!(writer.lookup(foo_bar).unwrap(), filepath!("foo.bar").into());
            {
                let mut foo_bar = writer.lookup_iter(foo_bar).unwrap();
                assert_eq!(
                    foo_bar.file_name,
                    FileName::WithExtension {
                        extension: nestr!("bar"),
                        file_stem: Some(nestr!("foo"))
                    }
                );
                assert!(foo_bar.file_path.next().is_none());
            }

            // bar |= `SubpathFlags::FileOrFolderName`
            let bar = writer.insert(filepath!("foo/bar")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 2);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 6);
            assert_eq!(writer.lookup(bar).unwrap(), filepath!("foo/bar").into());
            {
                let bar = writer.lookup_iter(bar).unwrap();
                assert_eq!(bar.file_name, FileName::NoExtension(nestr!("bar")));
                assert!(bar.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            writer.clear();
        }

        {
            // Reuse extension "txt" as file name (and file stem "bar" as folder name).

            // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
            // bar: `SubpathFlags::FileStem`
            // txt: `SubpathFlags::Extension`
            let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(
                writer.lookup(bar_txt).unwrap(),
                filepath!("foo/bar.txt").into()
            );
            {
                let bar_txt = writer.lookup_iter(bar_txt).unwrap();
                assert_eq!(
                    bar_txt.file_name,
                    FileName::WithExtension {
                        extension: nestr!("txt"),
                        file_stem: Some(nestr!("bar"))
                    }
                );
                assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            // bar |= `SubpathFlags::FileOrFolderName`
            // txt |= `SubpathFlags::FileOrFolderName`
            let txt = writer.insert(filepath!("foo/bar/txt")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 3);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(writer.lookup(txt).unwrap(), filepath!("foo/bar/txt").into());
            {
                let txt = writer.lookup_iter(txt).unwrap();
                assert_eq!(txt.file_name, FileName::NoExtension(nestr!("txt")));
                assert!(txt
                    .file_path
                    .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
            }

            writer.clear();
        }
    }

    #[test]
    fn reuse_file_name_as_folder_name() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        // Reuse file name "bar" as folder name -> `FileAlreadyExistsAtFolderPath("foo/bar")`

        // subpaths: [ hash("foo"), hash("foo", "bar") ]
        // bar: `SubpathFlags::FileOrFolderName`
        let bar = writer.insert(filepath!("foo/bar")).unwrap();
        assert_eq!(writer.len(), 1);
        assert_eq!(writer.num_components(), 2);
        assert_eq!(writer.num_subpaths(), 2);
        assert_eq!(writer.num_extensions(), 0);
        assert_eq!(writer.string_len(), 6);
        assert_eq!(writer.lookup(bar).unwrap(), filepath!("foo/bar").into());
        {
            let bar = writer.lookup_iter(bar).unwrap();
            assert_eq!(bar.file_name, FileName::NoExtension(nestr!("bar")));
            assert!(bar.file_path.eq(vec![nestr!("foo")].into_iter()));
        }
        assert_eq!(
            writer.insert(filepath!("foo/bar/txt")).err().unwrap(),
            FileTreeWriterError::FileAlreadyExistsAtFolderPath(filepath!("foo/bar").into())
        );
    }

    #[test]
    fn reuse_folder_name_as_folder_name() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        // Reuse folder names "foo", "bar" as folder names (the usual case).

        // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
        // foo, bar: `SubpathFlags::FileOrFolderName`
        let txt = writer.insert(filepath!("foo/bar/txt")).unwrap();
        assert_eq!(writer.len(), 1);
        assert_eq!(writer.num_components(), 3);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 0);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(writer.lookup(txt).unwrap(), filepath!("foo/bar/txt").into());
        {
            let txt = writer.lookup_iter(txt).unwrap();
            assert_eq!(txt.file_name, FileName::NoExtension(nestr!("txt")));
            assert!(txt
                .file_path
                .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
        }

        let cfg = writer.insert(filepath!("foo/bar/cfg")).unwrap();
        assert_eq!(writer.len(), 2);
        assert_eq!(writer.num_components(), 4);
        assert_eq!(writer.num_subpaths(), 4);
        assert_eq!(writer.num_extensions(), 0);
        assert_eq!(writer.string_len(), 12);
        assert_eq!(writer.lookup(cfg).unwrap(), filepath!("foo/bar/cfg").into());
        {
            let cfg = writer.lookup_iter(cfg).unwrap();
            assert_eq!(cfg.file_name, FileName::NoExtension(nestr!("cfg")));
            assert!(cfg
                .file_path
                .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
        }
    }

    #[test]
    fn reuse_file_stem_as_folder_name() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        // Reuse file stem "bar" as folder name (and extension "txt" as file name).

        // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
        // bar: `SubpathFlags::FileStem`
        // txt: `SubpathFlags::Extension`
        let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
        assert_eq!(writer.len(), 1);
        assert_eq!(writer.num_components(), 2);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 1);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(
            writer.lookup(bar_txt).unwrap(),
            filepath!("foo/bar.txt").into()
        );
        {
            let bar_txt = writer.lookup_iter(bar_txt).unwrap();
            assert_eq!(
                bar_txt.file_name,
                FileName::WithExtension {
                    extension: nestr!("txt"),
                    file_stem: Some(nestr!("bar"))
                }
            );
            assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
        }

        // bar |= `SubpathFlags::FileOrFolderName`
        // txt |= `SubpathFlags::FileOrFolderName`
        let txt = writer.insert(filepath!("foo/bar/txt")).unwrap();
        assert_eq!(writer.len(), 2);
        assert_eq!(writer.num_components(), 3);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 1);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(writer.lookup(txt).unwrap(), filepath!("foo/bar/txt").into());
        {
            let txt = writer.lookup_iter(txt).unwrap();
            assert_eq!(txt.file_name, FileName::NoExtension(nestr!("txt")));
            assert!(txt
                .file_path
                .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
        }
    }

    #[test]
    fn reuse_extension_as_folder_name() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        {
            // Reuse extension "bar" as folder name (and file stem "foo" as folder name).

            // subpaths: [ hash("foo"), hash("foo", "bar") ]
            // bar: `SubpathFlags::Extension`
            let foo_bar = writer.insert(filepath!("foo.bar")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 1);
            assert_eq!(writer.num_subpaths(), 2);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 6);
            assert_eq!(writer.lookup(foo_bar).unwrap(), filepath!("foo.bar").into());
            {
                let mut foo_bar = writer.lookup_iter(foo_bar).unwrap();
                assert_eq!(
                    foo_bar.file_name,
                    FileName::WithExtension {
                        extension: nestr!("bar"),
                        file_stem: Some(nestr!("foo"))
                    }
                );
                assert!(foo_bar.file_path.next().is_none());
            }

            // foo |= `SubpathFlags::FileOrFolderName`
            // bar |= `SubpathFlags::FileOrFolderName`
            let txt = writer.insert(filepath!("foo/bar/txt")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 3);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(writer.lookup(txt).unwrap(), filepath!("foo/bar/txt").into());
            {
                let txt = writer.lookup_iter(txt).unwrap();
                assert_eq!(txt.file_name, FileName::NoExtension(nestr!("txt")));
                assert!(txt
                    .file_path
                    .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
            }

            writer.clear();
        }

        {
            // Reuse extension "txt" as folder name name (and file stem "bar" as folder name).

            // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
            // bar: `SubpathFlags::FileStem`
            // txt: `SubpathFlags::Extension`
            let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(
                writer.lookup(bar_txt).unwrap(),
                filepath!("foo/bar.txt").into()
            );
            {
                let bar_txt = writer.lookup_iter(bar_txt).unwrap();
                assert_eq!(
                    bar_txt.file_name,
                    FileName::WithExtension {
                        extension: nestr!("txt"),
                        file_stem: Some(nestr!("bar"))
                    }
                );
                assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            // bar |= `SubpathFlags::FileOrFolderName`
            // txt |= `SubpathFlags::FileOrFolderName`
            let cfg = writer.insert(filepath!("foo/bar/txt/cfg")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 4);
            assert_eq!(writer.num_subpaths(), 4);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 12);
            assert_eq!(
                writer.lookup(cfg).unwrap(),
                filepath!("foo/bar/txt/cfg").into()
            );
            {
                let cfg = writer.lookup_iter(cfg).unwrap();
                assert_eq!(cfg.file_name, FileName::NoExtension(nestr!("cfg")));
                assert!(cfg
                    .file_path
                    .eq(vec![nestr!("txt"), nestr!("bar"), nestr!("foo")].into_iter()));
            }

            writer.clear();
        }
    }

    #[test]
    fn reuse_file_name_as_file_stem() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        // Reuse file name "bar" as file stem.

        // subpaths: [ hash("foo"), hash("foo", "bar") ]
        // bar: `SubpathFlags::FileOrFolderName`
        let bar = writer.insert(filepath!("foo/bar")).unwrap();
        assert_eq!(writer.len(), 1);
        assert_eq!(writer.num_components(), 2);
        assert_eq!(writer.num_subpaths(), 2);
        assert_eq!(writer.num_extensions(), 0);
        assert_eq!(writer.string_len(), 6);
        assert_eq!(writer.lookup(bar).unwrap(), filepath!("foo/bar").into());
        {
            let bar = writer.lookup_iter(bar).unwrap();
            assert_eq!(bar.file_name, FileName::NoExtension(nestr!("bar")));
            assert!(bar.file_path.eq(vec![nestr!("foo")].into_iter()));
        }

        // bar |= `SubpathFlags::FileStem`
        let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
        assert_eq!(writer.len(), 2);
        assert_eq!(writer.num_components(), 2);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 1);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(
            writer.lookup(bar_txt).unwrap(),
            filepath!("foo/bar.txt").into()
        );
        {
            let bar_txt = writer.lookup_iter(bar_txt).unwrap();
            assert_eq!(
                bar_txt.file_name,
                FileName::WithExtension {
                    extension: nestr!("txt"),
                    file_stem: Some(nestr!("bar"))
                }
            );
            assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
        }
    }

    #[test]
    fn reuse_folder_name_as_file_stem() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        // Reuse folder name "bar" as file stem (and file name "txt" as extension).

        // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
        // bar: `SubpathFlags::FileOrFolderName`
        // txt: `SubpathFlags::FileOrFolderName`
        let txt = writer.insert(filepath!("foo/bar/txt")).unwrap();
        assert_eq!(writer.len(), 1);
        assert_eq!(writer.num_components(), 3);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 0);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(writer.lookup(txt).unwrap(), filepath!("foo/bar/txt").into());
        {
            let txt = writer.lookup_iter(txt).unwrap();
            assert_eq!(txt.file_name, FileName::NoExtension(nestr!("txt")));
            assert!(txt
                .file_path
                .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
        }

        // bar |= `SubpathFlags::FileStem`
        // txt |= `SubpathFlags::Extension`
        let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
        assert_eq!(writer.len(), 2);
        assert_eq!(writer.num_components(), 3);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 1);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(
            writer.lookup(bar_txt).unwrap(),
            filepath!("foo/bar.txt").into()
        );
        {
            let bar_txt = writer.lookup_iter(bar_txt).unwrap();
            assert_eq!(
                bar_txt.file_name,
                FileName::WithExtension {
                    extension: nestr!("txt"),
                    file_stem: Some(nestr!("bar"))
                }
            );
            assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
        }
    }

    #[test]
    fn reuse_file_stem_as_file_stem() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        {
            // Reuse file stem "bar" as file stem.

            // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
            // bar: `SubpathFlags::Extension`
            let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(
                writer.lookup(bar_txt).unwrap(),
                filepath!("foo/bar.txt").into()
            );
            {
                let bar_txt = writer.lookup_iter(bar_txt).unwrap();
                assert_eq!(
                    bar_txt.file_name,
                    FileName::WithExtension {
                        extension: nestr!("txt"),
                        file_stem: Some(nestr!("bar"))
                    }
                );
                assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            // subpaths += hash("foo", "bar", "cfg")
            let bar_cfg = writer.insert(filepath!("foo/bar.cfg")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 4);
            assert_eq!(writer.num_extensions(), 2);
            assert_eq!(writer.string_len(), 12);
            assert_eq!(
                writer.lookup(bar_cfg).unwrap(),
                filepath!("foo/bar.cfg").into()
            );
            {
                let bar_cfg = writer.lookup_iter(bar_cfg).unwrap();
                assert_eq!(
                    bar_cfg.file_name,
                    FileName::WithExtension {
                        extension: nestr!("cfg"),
                        file_stem: Some(nestr!("bar"))
                    }
                );
                assert!(bar_cfg.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            writer.clear();
        }

        {
            // Reuse empty file stem "" as file stem.

            // subpaths: [ hash("foo"), hash("foo", ""), hash("foo", "", "txt") ]
            // bar: `SubpathFlags::Extension`
            let _txt = writer.insert(filepath!("foo/.txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 6);
            assert_eq!(writer.lookup(_txt).unwrap(), filepath!("foo/.txt").into());
            {
                let _txt = writer.lookup_iter(_txt).unwrap();
                assert_eq!(
                    _txt.file_name,
                    FileName::WithExtension {
                        extension: nestr!("txt"),
                        file_stem: None
                    }
                );
                assert!(_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            // subpaths += hash("foo", "", "cfg")
            let _cfg = writer.insert(filepath!("foo/.cfg")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 4);
            assert_eq!(writer.num_extensions(), 2);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(writer.lookup(_cfg).unwrap(), filepath!("foo/.cfg").into());
            {
                let _cfg = writer.lookup_iter(_cfg).unwrap();
                assert_eq!(
                    _cfg.file_name,
                    FileName::WithExtension {
                        extension: nestr!("cfg"),
                        file_stem: None
                    }
                );
                assert!(_cfg.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            writer.clear();
        }
    }

    #[test]
    fn reuse_extension_as_file_stem() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        // Reuse extension "txt" as file stem (and file stem "bar" as folder name).

        // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
        // bar: `SubpathFlags::FileStem`
        // txt: `SubpathFlags::Extension`
        let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
        assert_eq!(writer.len(), 1);
        assert_eq!(writer.num_components(), 2);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 1);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(
            writer.lookup(bar_txt).unwrap(),
            filepath!("foo/bar.txt").into()
        );
        {
            let bar_txt = writer.lookup_iter(bar_txt).unwrap();
            assert_eq!(
                bar_txt.file_name,
                FileName::WithExtension {
                    extension: nestr!("txt"),
                    file_stem: Some(nestr!("bar"))
                }
            );
            assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
        }

        // subpaths += hash("foo", "bar", "txt", "cfg")
        // bar |= `SubpathFlags::FileOrFolderName`
        // txt |= `SubpathFlags::FileStem`
        let txt_cfg = writer.insert(filepath!("foo/bar/txt.cfg")).unwrap();
        assert_eq!(writer.len(), 2);
        assert_eq!(writer.num_components(), 3);
        assert_eq!(writer.num_subpaths(), 4);
        assert_eq!(writer.num_extensions(), 2);
        assert_eq!(writer.string_len(), 12);
        assert_eq!(
            writer.lookup(txt_cfg).unwrap(),
            filepath!("foo/bar/txt.cfg").into()
        );
        {
            let txt_cfg = writer.lookup_iter(txt_cfg).unwrap();
            assert_eq!(
                txt_cfg.file_name,
                FileName::WithExtension {
                    extension: nestr!("cfg"),
                    file_stem: Some(nestr!("txt"))
                }
            );
            assert!(txt_cfg
                .file_path
                .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
        }

        writer.clear();
    }

    #[test]
    fn reuse_file_name_as_extension() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        {
            // Reuse file name "bar" as extension (and folder name "foo" as file stem).

            // subpaths: [ hash("foo"), hash("foo", "bar") ]
            // foo: `SubpathFlags::FileOrFolderName`
            // bar: `SubpathFlags::FileOrFolderName`
            let bar = writer.insert(filepath!("foo/bar")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 2);
            assert_eq!(writer.num_extensions(), 0);
            assert_eq!(writer.string_len(), 6);
            assert_eq!(writer.lookup(bar).unwrap(), filepath!("foo/bar").into());
            {
                let bar = writer.lookup_iter(bar).unwrap();
                assert_eq!(bar.file_name, FileName::NoExtension(nestr!("bar")));
                assert!(bar.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            // foo |= `SubpathFlags::FileStem`
            // bar |= `SubpathFlags::Extension`
            let foo_bar = writer.insert(filepath!("foo.bar")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 2);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 6);
            assert_eq!(writer.lookup(foo_bar).unwrap(), filepath!("foo.bar").into());
            {
                let mut foo_bar = writer.lookup_iter(foo_bar).unwrap();
                assert_eq!(
                    foo_bar.file_name,
                    FileName::WithExtension {
                        extension: nestr!("bar"),
                        file_stem: Some(nestr!("foo"))
                    }
                );
                assert!(foo_bar.file_path.next().is_none());
            }

            writer.clear();
        }

        {
            // Reuse file name "txt" as extension (and folder name "bar" as file stem).

            // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
            // bar: `SubpathFlags::FileOrFolderName`
            // txt: `SubpathFlags::FileOrFolderName`
            let txt = writer.insert(filepath!("foo/bar/txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 3);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 0);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(writer.lookup(txt).unwrap(), filepath!("foo/bar/txt").into());
            {
                let txt = writer.lookup_iter(txt).unwrap();
                assert_eq!(txt.file_name, FileName::NoExtension(nestr!("txt")));
                assert!(txt
                    .file_path
                    .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
            }

            // bar |= `SubpathFlags::FileStem`
            // txt |= `SubpathFlags::Extension`
            let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 3);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(
                writer.lookup(bar_txt).unwrap(),
                filepath!("foo/bar.txt").into()
            );
            {
                let bar_txt = writer.lookup_iter(bar_txt).unwrap();
                assert_eq!(
                    bar_txt.file_name,
                    FileName::WithExtension {
                        extension: nestr!("txt"),
                        file_stem: Some(nestr!("bar"))
                    }
                );
                assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            writer.clear();
        }
    }

    #[test]
    fn reuse_folder_name_as_extension() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        {
            // Reuse folder name "bar" as extension (and folder name "foo" as file stem).

            // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
            // foo: `SubpathFlags::FileOrFolderName`
            // bar: `SubpathFlags::FileOrFolderName`
            let txt = writer.insert(filepath!("foo/bar/txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 3);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 0);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(writer.lookup(txt).unwrap(), filepath!("foo/bar/txt").into());
            {
                let txt = writer.lookup_iter(txt).unwrap();
                assert_eq!(txt.file_name, FileName::NoExtension(nestr!("txt")));
                assert!(txt
                    .file_path
                    .eq(vec![nestr!("bar"), nestr!("foo")].into_iter()));
            }

            // foo |= `SubpathFlags::FileStem`
            // bar |= `SubpathFlags::Extension`
            let foo_bar = writer.insert(filepath!("foo.bar")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 3);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(writer.lookup(foo_bar).unwrap(), filepath!("foo.bar").into());
            {
                let mut foo_bar = writer.lookup_iter(foo_bar).unwrap();
                assert_eq!(
                    foo_bar.file_name,
                    FileName::WithExtension {
                        extension: nestr!("bar"),
                        file_stem: Some(nestr!("foo"))
                    }
                );
                assert!(foo_bar.file_path.next().is_none());
            }

            writer.clear();
        }

        {
            // Reuse folder name "txt" as extension (and folder name "bar" as file stem).

            // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt"), hash("foo", "bar", "txt", "cfg") ]
            // bar: `SubpathFlags::FileOrFolderName`
            // txt: `SubpathFlags::FileOrFolderName`
            let cfg = writer.insert(filepath!("foo/bar/txt/cfg")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 4);
            assert_eq!(writer.num_subpaths(), 4);
            assert_eq!(writer.num_extensions(), 0);
            assert_eq!(writer.string_len(), 12);
            assert_eq!(
                writer.lookup(cfg).unwrap(),
                filepath!("foo/bar/txt/cfg").into()
            );
            {
                let cfg = writer.lookup_iter(cfg).unwrap();
                assert_eq!(cfg.file_name, FileName::NoExtension(nestr!("cfg")));
                assert!(cfg
                    .file_path
                    .eq(vec![nestr!("txt"), nestr!("bar"), nestr!("foo")].into_iter()));
            }

            // bar |= `SubpathFlags::FileStem`
            // txt |= `SubpathFlags::Extension`
            let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
            assert_eq!(writer.len(), 2);
            assert_eq!(writer.num_components(), 4);
            assert_eq!(writer.num_subpaths(), 4);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 12);
            assert_eq!(
                writer.lookup(bar_txt).unwrap(),
                filepath!("foo/bar.txt").into()
            );
            {
                let bar_txt = writer.lookup_iter(bar_txt).unwrap();
                assert_eq!(
                    bar_txt.file_name,
                    FileName::WithExtension {
                        extension: nestr!("txt"),
                        file_stem: Some(nestr!("bar"))
                    }
                );
                assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
            }

            writer.clear();
        }
    }

    #[test]
    fn reuse_file_stem_as_extension() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        // Reuse file stem "bar" as extension (and folder name "foo" as file stem).

        // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
        // foo: `SubpathFlags::FileOrFolderName`
        // bar: `SubpathFlags::FileStem`
        let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
        assert_eq!(writer.len(), 1);
        assert_eq!(writer.num_components(), 2);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 1);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(
            writer.lookup(bar_txt).unwrap(),
            filepath!("foo/bar.txt").into()
        );
        {
            let bar_txt = writer.lookup_iter(bar_txt).unwrap();
            assert_eq!(
                bar_txt.file_name,
                FileName::WithExtension {
                    extension: nestr!("txt"),
                    file_stem: Some(nestr!("bar"))
                }
            );
            assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
        }

        // foo |= `SubpathFlags::FileStem`
        // bar |= `SubpathFlags::Extension`
        let foo_bar = writer.insert(filepath!("foo.bar")).unwrap();
        assert_eq!(writer.len(), 2);
        assert_eq!(writer.num_components(), 2);
        assert_eq!(writer.num_subpaths(), 3);
        assert_eq!(writer.num_extensions(), 2);
        assert_eq!(writer.string_len(), 9);
        assert_eq!(writer.lookup(foo_bar).unwrap(), filepath!("foo.bar").into());
        {
            let mut foo_bar = writer.lookup_iter(foo_bar).unwrap();
            assert_eq!(
                foo_bar.file_name,
                FileName::WithExtension {
                    extension: nestr!("bar"),
                    file_stem: Some(nestr!("foo"))
                }
            );
            assert!(foo_bar.file_path.next().is_none());
        }
    }

    #[test]
    fn reuse_extension_as_extension() {
        let mut writer = FileTreeWriter::new(BuildSeaHasher);

        {
            // Reuse extension "txt" as extension -> cannot happen, handled earlier by `PathAlreadyExists`

            // subpaths: [ hash("foo"), hash("foo", "bar"), hash("foo", "bar", "txt") ]
            // bar: `SubpathFlags::FileOrFolderName`
            let bar_txt = writer.insert(filepath!("foo/bar.txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 9);
            assert_eq!(
                writer.lookup(bar_txt).unwrap(),
                filepath!("foo/bar.txt").into()
            );
            {
                let bar_txt = writer.lookup_iter(bar_txt).unwrap();
                assert_eq!(
                    bar_txt.file_name,
                    FileName::WithExtension {
                        extension: nestr!("txt"),
                        file_stem: Some(nestr!("bar"))
                    }
                );
                assert!(bar_txt.file_path.eq(vec![nestr!("foo")].into_iter()));
            }
            assert_eq!(
                writer.insert(filepath!("foo/bar.txt")).err().unwrap(),
                FileTreeWriterError::PathAlreadyExists
            );

            writer.clear();
        }

        {
            // Reuse extension "txt" as extension -> cannot happen, handled earlier by `PathAlreadyExists`

            // subpaths: [ hash("foo.bar"), hash("foo.bar", "baz"), hash("foo.bar", "baz", "txt") ]
            // bar: `SubpathFlags::FileOrFolderName`
            let baz_txt = writer.insert(filepath!("foo.bar/baz.txt")).unwrap();
            assert_eq!(writer.len(), 1);
            assert_eq!(writer.num_components(), 2);
            assert_eq!(writer.num_subpaths(), 3);
            assert_eq!(writer.num_extensions(), 1);
            assert_eq!(writer.string_len(), 13);
            assert_eq!(
                writer.lookup(baz_txt).unwrap(),
                filepath!("foo.bar/baz.txt").into()
            );
            {
                let baz_txt = writer.lookup_iter(baz_txt).unwrap();
                assert_eq!(
                    baz_txt.file_name,
                    FileName::WithExtension {
                        extension: nestr!("txt"),
                        file_stem: Some(nestr!("baz"))
                    }
                );
                assert!(baz_txt.file_path.eq(vec![nestr!("foo.bar")].into_iter()));
            }
            assert_eq!(
                writer.insert(filepath!("foo.bar/baz.txt")).err().unwrap(),
                FileTreeWriterError::PathAlreadyExists
            );

            writer.clear();
        }
    }
}

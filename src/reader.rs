use {
    crate::*,
    minifilepath::{is_valid_path_component, FilePathBuf, FilePathBuilder},
    ministr::NonEmptyStr,
    std::{
        collections::{HashMap, HashSet},
        iter::Iterator,
        mem, slice, str,
    },
};

/// Provides an API to lookup [`file paths`](FilePathBuf) by their [`hashes`](PathHash)
/// in the data blob [`written`](FileTreeWriter::write) by the [`FileTreeWriter`].
pub struct FileTreeReader<'a> {
    data: &'a [u8],
    lookup: Option<HashMap<PathHash, LeafPathComponent>>,
}

impl<'a> FileTreeReader<'a> {
    /// Creates a [`FileTreeReader`] from the `data` blob [`written`](FileTreeWriter#method.write) by the [`FileTreeWriter`].
    /// Attempts to validate the `data` blob and returns `None` if `data` is not a valid file tree data blob.
    pub fn new(data: &'a [u8]) -> Option<Self> {
        if !Self::validate_blob(&data) {
            return None;
        }

        Some(Self { data, lookup: None })
    }

    /// Creates a [`FileTreeReader`] from the `data` blob [`written`](struct.FileTreeWriter.html#method.write) by the [`FileTreeWriter`].
    ///
    /// # Safety
    ///
    /// Unsafe because no validation is performed of the `data` blob.
    /// The caller guarantees that `data` is a valid file tree data blob (i.e. [`is_valid`](#method.is_valid) returned `true` for it).
    pub unsafe fn new_unchecked(data: &'a [u8]) -> Self {
        // TODO: still doing a sanity check in debug configuration just in case. Remove if/when this becomes an issue.
        debug_assert!(
            Self::validate_blob(data),
            "tried to create a `FileTreeReader` from an invalid data blob"
        );
        Self { data, lookup: None }
    }

    /// Returns `true` if `data` is a valid file tree data blob, [`written`](struct.FileTreeWriter.html#method.write) by the [`FileTreeWriter`].
    pub fn is_valid(data: &'a [u8]) -> bool {
        Self::validate_blob(data)
    }

    /// (Optionally) builds the hashmap to accelerate lookups.
    /// Call once after creating the [`FileTreeReader`].
    ///
    /// Provides `O(1)` lookups at the cost of extra memory.
    /// Otherwise lookups are `O(n)`.
    pub fn build_lookup(&mut self) {
        if self.lookup.is_none() {
            let header = unsafe { Self::header(self.data) };

            let lookup_len = header.lookup_len();

            let path_hashes = unsafe { Self::path_hashes(self.data, lookup_len) };
            let lpcs = unsafe { Self::leaf_path_components(self.data, lookup_len) };

            self.lookup.replace(
                path_hashes
                    .iter()
                    .zip(lpcs.iter())
                    .map(|(k, v)| (u64_from_bin(*k), v.unpack()))
                    .collect(),
            );
        }
    }

    /// Returns the user-provided "version" from the header, as written by [`FileTreeWriter::write`] / [`FileTreeWriter::write_to_vec`].
    pub fn version(&self) -> u64 {
        let header = unsafe { Self::header(self.data) };

        header.version()
    }

    /// Returns the number of [`file paths`](FilePath) in the reader.
    pub fn len(&self) -> usize {
        let header = unsafe { Self::header(self.data) };

        header.lookup_len() as _
    }

    /*
    /// Returns the number of unique interned strings in the reader.
    pub fn num_strings(&self) -> usize {
        let header = unsafe { Self::header(self.data) };

        header.string_table_len() as _
    }
    */

    /// Returns the total length in bytes of all unique interned strings in the reader.
    pub fn string_len(&self) -> u64 {
        let header = unsafe { Self::header(self.data) };

        let string_section_start = Self::string_section_start(
            header.lookup_len(),
            header.path_components_len(),
            header.extension_table_len(),
            header.string_table_len(),
        );
        debug_assert!(string_section_start < self.data.len() as u64);

        let string_section_end = self.data.len() as u64;

        string_section_end - string_section_start
    }

    /// Returns [`the file name and a reverse (leaf to root) iterator`](FilePathIter) over folder name [`path components`](FilePathComponent)
    /// of the [`file path`](minifilepath::FilePath) associated with the path `hash`, if any.
    pub fn lookup_iter(
        &self,
        hash: PathHash,
    ) -> Option<FilePathIter<'_, impl Iterator<Item = FilePathComponent<'_>>>> {
        let header = unsafe { Self::header(self.data) };

        self.lookup_leaf_path_component(header, hash)
            .map(|lpc| self.iter(header, lpc))
    }

    /// Attempts to fill the `builder` with the [`file path`](FilePathBuf) associated with the file path `hash`, if any.
    ///
    /// Returns the `builder` back if the path `hash` does not have a [`file path`](FilePathBuf) associated with it.
    pub fn lookup_into(
        &self,
        hash: PathHash,
        builder: FilePathBuilder,
    ) -> Result<FilePathBuf, FilePathBuilder> {
        let header = unsafe { Self::header(self.data) };

        if let Some(lpc) = self.lookup_leaf_path_component(header, hash) {
            Ok(self.build_path_string(header, lpc, builder))
        } else {
            Err(builder)
        }
    }

    /// Returns the [`file path`](FilePathBuf) associated with the file path `hash`, if any.
    pub fn lookup(&self, hash: PathHash) -> Option<FilePathBuf> {
        self.lookup_into(hash, FilePathBuilder::new()).ok()
    }

    /// The caller guarantees the `data` is at least large enough to hold a `FileTreeHeader`.
    unsafe fn header(data: &[u8]) -> &FileTreeHeader {
        &*(data.as_ptr() as *const _)
    }

    // Attempts to validate the `data` to make sure it is a valid file tree blob, written by the `FileTreeWriter`.
    fn validate_blob(data: &[u8]) -> bool {
        // Check if the data is at least large enough to hold the smallest possible file tree blob.
        if (data.len() as u64) < Self::min_size() {
            return false;
        }

        // Safe because we made sure the `data` is large enough for at least a header.
        let header = unsafe { Self::header(data) };

        // Check the header magic.
        if !header.check_magic() {
            return false;
        }

        let lookup_len = header.lookup_len();
        let path_components_len = header.path_components_len();
        let extension_table_len = header.extension_table_len();
        let string_table_len = header.string_table_len();

        // Must have at least as many (or more) path components as there are leaf path components.
        if path_components_len < lookup_len {
            return false;
        }

        // Must have as many (or more) leaf path components as there are extensions.
        if lookup_len < extension_table_len as _ {
            return false;
        }

        // Must have at least as many (or more) path components as there are strings.
        if path_components_len < string_table_len {
            return false;
        }

        // Must be large enough to accomodate the section lengths from the header.
        if (data.len() as u64)
            < Self::required_size(
                lookup_len,
                path_components_len,
                extension_table_len,
                string_table_len,
            )
        {
            return false;
        }

        /*
                // Assume the lookup keys (path hashes) are valid.
                let lookup_keys = unsafe { Self::lookup_keys(data, lookup_len) };

                // All entries must be unique.
                #[cfg(debug_assertions)]
                if Self::has_duplicates_quadratic(lookup_keys) {
                    return false;
                }
        */

        // Assume the path components are valid.
        // Safe because we made sure the `data` is large enough.
        let path_components =
            unsafe { Self::path_components(data, lookup_len, path_components_len) };

        for path_component in path_components.iter().map(PackedPathComponent::unpack) {
            // Make sure all string indices are within the valid range.
            if path_component.string >= string_table_len {
                return false;
            }

            // Make sure all parent indices are within the valid range.
            if let Some(parent) = path_component.parent {
                if parent >= path_components_len {
                    return false;
                }
            }
        }

        // Assume the extensions are valid.
        // Safe because we made sure the `data` is large enough.
        let extension_table = unsafe {
            Self::extension_table(data, lookup_len, path_components_len, extension_table_len)
        };

        // Make sure all extension string indices are within the valid range.
        if extension_table
            .iter()
            .any(|&extension| extension >= string_table_len)
        {
            return false;
        }

        /*
            // All entries must be unique.
            #[cfg(debug_assertions)]
            if Self::has_duplicates_quadratic(extension_table) {
                return false;
            }
        */

        // Assume the string table is valid.
        // Safe because we made sure the `data` is large enough.
        let string_table = unsafe {
            Self::string_table(
                data,
                lookup_len,
                path_components_len,
                extension_table_len,
                string_table_len,
            )
        };

        /*
                // All entries must be unique.
                #[cfg(debug_assertions)]
                if Self::has_duplicates_quadratic(string_table) {
                    return false;
                }
        */

        let string_section_start = Self::string_section_start(
            lookup_len,
            path_components_len,
            extension_table_len,
            string_table_len,
        );
        debug_assert!(string_section_start < data.len() as StringOffset);

        let string_section_end = data.len() as StringOffset;

        for string in string_table.iter().map(PackedInternedString::unpack) {
            // Empty strings are allowed (empty file stems), and must have offset == `0`.
            if string.len == 0 {
                if string.offset != 0 {
                    return false;
                }
            } else {
                // Make sure all string offsets and lengths in the string table are within the valid range.
                if string.offset < string_section_start as _ {
                    return false;
                }

                if string.offset + string.len as StringOffset > string_section_end {
                    return false;
                }
            }

            // Make sure all strings are valid UTF-8.
            if let Ok(string) =
                str::from_utf8(unsafe { Self::slice(data, string.offset, string.len as _) })
            {
                if let Some(string) = NonEmptyStr::new(string) {
                    // Make sure all strings are valid path components.
                    if !is_valid_path_component(string) {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }

        // Assume the lookup values (leaf path components) are valid.
        // Safe because we made sure the `data` is large enough.
        let lpcs = unsafe { Self::leaf_path_components(data, lookup_len) };

        /*
                // All entries must be unique.
                #[cfg(debug_assertions)]
                if Self::has_duplicates_quadratic(lpcs) {
                    return false;
                }
        */

        let string_section_len = string_section_end - string_section_start;

        // Used to detect loops in the file tree.
        let mut visited_components = HashSet::<PathComponentIndex>::new();

        for lpc in lpcs.iter().map(PackedLeafPathComponent::unpack) {
            // Make sure all path component indices are within the valid range.
            if lpc.path_component >= path_components_len {
                return false;
            }

            // Make sure all extension indices are within the valid range.
            if let Some(extension) = lpc.extension {
                if extension > extension_table_len {
                    return false;
                }
            }

            if (lpc.string_len as StringOffset) > string_section_len {
                return false;
            }

            // Check for cycles starting at this leaf path component.
            // Validate that extension components have file stem components.
            {
                visited_components.clear();

                // String length obtained from iterating the path must match its declared value.
                let mut actual_len: FullStringLength = 0;

                let mut cur_path_component = lpc.path_component;
                visited_components.insert(cur_path_component);

                let mut first = true;

                loop {
                    // Safe because we made sure all component indices are valid.
                    debug_assert!((cur_path_component as usize) < path_components.len());
                    let path_component =
                        unsafe { path_components.get_unchecked(cur_path_component as usize) }
                            .unpack();

                    // Check the extension, if any.
                    if first {
                        if let Some(extension) = lpc.extension {
                            // Safe because we made sure all extension indices are valid.
                            debug_assert!(extension < extension_table_len);
                            let extension_string_index =
                                Self::extension_string_index_impl(data, header, extension);
                            // Safe because we made sure all extension string indices are valid.
                            debug_assert!(extension_string_index < string_table_len);
                            let extension_string = unsafe {
                                string_table.get_unchecked(extension_string_index as usize)
                            }
                            .unpack();
                            actual_len += extension_string.len as FullStringLength;
                            // Count the dot.
                            actual_len += 1;
                        }

                        first = false;
                    }

                    // Safe because we made sure all string indices are valid.
                    debug_assert!(path_component.string < string_table_len);
                    let string =
                        unsafe { string_table.get_unchecked(path_component.string as usize) }
                            .unpack();

                    actual_len += string.len as FullStringLength;

                    // If the path component has a parent, keep processing.
                    if let Some(parent) = path_component.parent {
                        // Cycles are not allowed.
                        if !visited_components.insert(parent) {
                            return false;
                        }

                        cur_path_component = parent;
                        // Count the separator character.
                        actual_len += 1;

                    // Otherwise we've reached the root of the path; time to check whether string lengths match.
                    } else {
                        break;
                    }
                }

                if actual_len != lpc.string_len {
                    return false;
                }
            }
        }

        // Seems like all the offsets/lengths/indices in the blob are within valid ranges;
        // and all strings are valid UTF-8.
        // This at least guarantees all accesses to the data blob via the `FileTreeReader` will be memory-safe.

        true
    }

    /// Looks up the leaf path component associated with the file path `hash`, if any.
    fn lookup_leaf_path_component(
        &self,
        header: &FileTreeHeader,
        hash: PathHash,
    ) -> Option<LeafPathComponent> {
        if let Some(lookup) = &self.lookup {
            lookup.get(&hash).map(|lpc| *lpc)
        } else {
            let lookup_len = header.lookup_len();

            let path_hashes = unsafe { Self::path_hashes(self.data, lookup_len) };

            if let Some(idx) = path_hashes
                .iter()
                .cloned()
                .map(u64_from_bin)
                // TODO: binary search.
                .position(|key| key == hash)
            {
                let lpcs = unsafe { Self::leaf_path_components(self.data, lookup_len) };
                debug_assert!(idx < lpcs.len());
                Some(unsafe { lpcs.get_unchecked(idx) }.unpack())
            } else {
                None
            }
        }
    }

    /// Clears and fills the `builder` with the full path for the leaf path component `lpc`, using `/` as separators.
    fn build_path_string(
        &self,
        header: &FileTreeHeader,
        lpc: LeafPathComponent,
        builder: FilePathBuilder,
    ) -> FilePathBuf {
        let mut string = builder.into_inner();
        build_path_string(self.iter(header, lpc), lpc.string_len, &mut string);
        debug_assert!(!string.is_empty());
        unsafe { FilePathBuf::new_unchecked(string) }
    }

    /// Returns a file path iterator for the leaf path component `lpc`.
    /// The caller guarantees `lpc` is valid.
    fn iter(
        &self,
        header: &FileTreeHeader,
        lpc: LeafPathComponent,
    ) -> FilePathIter<'_, impl Iterator<Item = FilePathComponent<'_>>> {
        let path_component = self.path_component_impl(header, lpc.path_component);

        let file_name = if let Some(extension_index) = lpc.extension {
            // Extensions may not be empty.
            let extension = self.non_empty_string(self.extension_string_index(extension_index));
            // For leaf path components with an extension, `path_component` is for the file stem.
            // File stems may be empty.
            let file_stem = NonEmptyStr::new(self.string(path_component.string));

            FileName::WithExtension {
                extension,
                file_stem,
            }
        } else {
            // File names (with no extension) may not be empty.
            FileName::NoExtension(self.non_empty_string(path_component.string))
        };

        FilePathIter {
            file_name,
            file_path: FolderIter::new(
                self,
                path_component
                    .parent
                    .map(|parent| self.path_component_impl(header, parent)),
            ),
        }
    }

    /// The caller guarantees the path component `index` is valid.
    fn path_component(&self, index: PathComponentIndex) -> PathComponent {
        let header = unsafe { Self::header(self.data) };
        self.path_component_impl(header, index)
    }

    /// The caller guarantees the path component `index` is valid.
    fn path_component_impl(
        &self,
        header: &FileTreeHeader,
        index: PathComponentIndex,
    ) -> PathComponent {
        let path_components = unsafe {
            Self::path_components(self.data, header.lookup_len(), header.path_components_len())
        };
        debug_assert!(index < path_components.len() as _);
        unsafe { path_components.get_unchecked(index as usize) }.unpack()
    }

    /// The caller guarantees the string `index` is valid.
    fn string(&self, index: StringIndex) -> &str {
        let header = unsafe { Self::header(self.data) };

        let offset_and_len = {
            let string_table = unsafe {
                Self::string_table(
                    self.data,
                    header.lookup_len(),
                    header.path_components_len(),
                    header.extension_table_len(),
                    header.string_table_len(),
                )
            };
            debug_assert!((index as usize) < string_table.len());
            unsafe { string_table.get_unchecked(index as usize) }.unpack()
        };

        unsafe { Self::string_slice(self.data, offset_and_len.offset, offset_and_len.len) }
    }

    /// The caller guarantees the string `index` is valid,
    /// and that the string at `index` is non-empty (file stems may be empty).
    fn non_empty_string(&self, index: StringIndex) -> &NonEmptyStr {
        let s = self.string(index);
        debug_assert!(!s.is_empty());
        unsafe { NonEmptyStr::new_unchecked(s) }
    }

    /// The caller guarantees the extension `index` is valid,
    fn extension_string_index(&self, index: ExtensionIndex) -> StringIndex {
        let header = unsafe { Self::header(self.data) };
        Self::extension_string_index_impl(self.data, header, index)
    }

    /// The caller guarantees the extension `index` is valid,
    fn extension_string_index_impl(
        data: &[u8],
        header: &FileTreeHeader,
        index: ExtensionIndex,
    ) -> StringIndex {
        let extension_table = unsafe {
            Self::extension_table(
                data,
                header.lookup_len(),
                header.path_components_len(),
                header.extension_table_len(),
            )
        };
        debug_assert!((index as usize) < extension_table.len());
        *unsafe { extension_table.get_unchecked(index as usize) }
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the array of path hashes / lookup keys.
    const fn path_hashes_offset() -> u64 {
        // |Header|Path hashes|Leaf path components|Path components|Extension table|String table|Strings|
        //        ^
        //        |
        mem::size_of::<FileTreeHeader>() as _
    }

    /// Calculates the size in bytes of the path hashes / lookup keys array given the lookup length from the header.
    const fn path_hashes_size(lookup_len: PathComponentIndex) -> u64 {
        (lookup_len as u64) * (mem::size_of::<PathHash>() as u64)
    }

    /// Returns the subslice of lookup keys (path hashes) from the `data` blob.
    /// The caller guarantees `lookup_len` is valid for the `data` blob.
    unsafe fn path_hashes<'d>(data: &'d [u8], lookup_len: PathComponentIndex) -> &'d [PathHash] {
        Self::slice(data, Self::path_hashes_offset(), lookup_len as _)
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the array of lookup values.
    const fn leaf_path_components_offset(lookup_len: PathComponentIndex) -> u64 {
        // |Header|Path hashes|Leaf path components|Path components|Extension table|String table|Strings|
        //                    ^
        //                    |
        Self::path_hashes_offset() + Self::path_hashes_size(lookup_len)
    }

    /// Calculates the size in bytes of the leaf path components / lookup values array given the lookup length from the header.
    const fn leaf_path_components_size(lookup_len: PathComponentIndex) -> u64 {
        (lookup_len as u64) * (mem::size_of::<PackedLeafPathComponent>() as u64)
    }

    /// Returns the subslice of lookup values (leaf path components) from the `data` blob.
    /// The caller guarantees `lookup_len` is valid for the `data` blob.
    unsafe fn leaf_path_components<'d>(
        data: &'d [u8],
        lookup_len: PathComponentIndex,
    ) -> &'d [PackedLeafPathComponent] {
        Self::slice(
            data,
            Self::leaf_path_components_offset(lookup_len),
            lookup_len as _,
        )
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the array of path components.
    const fn path_components_offset(lookup_len: PathComponentIndex) -> u64 {
        // |Header|Path hashes|Leaf path components|Path components|Extension table|String table|Strings|
        //                                         ^
        //                                         |
        Self::leaf_path_components_offset(lookup_len) + Self::leaf_path_components_size(lookup_len)
    }

    /// Calculates the size in bytes of the path components array given its length from the header.
    const fn path_components_size(path_components_len: PathComponentIndex) -> u64 {
        (path_components_len as u64) * (mem::size_of::<PackedPathComponent>() as u64)
    }

    /// Returns the subslice of path components from the `data` blob.
    /// The caller guarantees `lookup_len` and `path_components_len` are valid for the `data` blob.
    unsafe fn path_components(
        data: &[u8],
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
    ) -> &[PackedPathComponent] {
        Self::slice(
            data,
            Self::path_components_offset(lookup_len),
            path_components_len as _,
        )
    }

    const fn extension_table_offset(
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
    ) -> u64 {
        // |Header|Path hashes|Leaf path components|Path components|Extension table|String table|Strings|
        //                                                         ^
        //                                                         |
        Self::path_components_offset(lookup_len) + Self::path_components_size(path_components_len)
    }

    /// Calculates the size in bytes of the extension table given its length from the header.
    const fn extension_table_size(extension_table_len: ExtensionIndex) -> u64 {
        (mem::size_of::<StringIndex>() as u64) * (extension_table_len as u64)
    }

    unsafe fn extension_table(
        data: &[u8],
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
        extension_table_len: ExtensionIndex,
    ) -> &[StringIndex] {
        Self::slice(
            data,
            Self::extension_table_offset(lookup_len, path_components_len),
            extension_table_len as _,
        )
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the string table.
    const fn string_table_offset(
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
        extension_table_len: ExtensionIndex,
    ) -> u64 {
        // |Header|Path hashes|Leaf path components|Path components|Extension table|String table|Strings|
        //                                                                         ^
        //                                                                         |
        let offset = Self::extension_table_offset(lookup_len, path_components_len)
            + Self::extension_table_size(extension_table_len);
        // Align to 8b.
        (offset + 7) / 8 * 8
    }

    /// Calculates the size in bytes of the string table given its length from the header.
    const fn string_table_size(string_table_len: StringIndex) -> u64 {
        (mem::size_of::<PackedInternedString>() as u64) * (string_table_len as u64)
    }

    /// Returns the subslice of string table entries from the `data` blob.
    /// The caller guarantees `lookup_len`, `path_components_len` and `string_table_len` are valid for the `data` blob.
    unsafe fn string_table(
        data: &[u8],
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
        extension_table_len: ExtensionIndex,
        string_table_len: StringIndex,
    ) -> &[PackedInternedString] {
        Self::slice(
            data,
            Self::string_table_offset(lookup_len, path_components_len, extension_table_len),
            string_table_len as _,
        )
    }

    /// Minimum size of the (variable length) string section given the string table length. Assumes 1-byte strings.
    const fn min_string_section_size(string_table_len: StringIndex) -> u64 {
        1 * string_table_len as u64
    }

    /// Minimum size of the valid file tree data blob.
    /// Header, 1 lookup entry, 1 path component entry, 0 extension entries, 1 string table entry, 1-byte string.
    fn min_size() -> u64 {
        Self::required_size(1, 1, 0, 1)
    }

    /// Calculates the required minimum data blob size in bytes for given section lengths from the header.
    fn required_size(
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
        extension_table_len: ExtensionIndex,
        string_table_len: StringIndex,
    ) -> u64 {
        Self::string_section_start(
            lookup_len,
            path_components_len,
            extension_table_len,
            string_table_len,
        ) + Self::min_string_section_size(string_table_len)
    }

    /// Calculates the offset in bytes to the (variable length) string section for given section lengths from the header.
    fn string_section_start(
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
        extension_table_len: ExtensionIndex,
        string_table_len: StringIndex,
    ) -> StringOffset {
        (mem::size_of::<FileTreeHeader>() as StringOffset)
            + Self::path_hashes_size(lookup_len)
            + Self::leaf_path_components_size(lookup_len)
            + Self::path_components_size(path_components_len)
            + Self::extension_table_size(extension_table_len)
            + Self::string_table_size(string_table_len)
    }

    /*
        #[cfg(debug_assertions)]
        fn has_duplicates_quadratic<T: Eq>(slice: &[T]) -> bool {
            if slice.len() < 2 {
                return false;
            }

            for (i, left) in slice[0..].iter().enumerate() {
                for right in &slice[i + 1..] {
                    if left == right {
                        return true;
                    }
                }
            }

            false
        }
    */

    /// Returns a UTF-8 string slice within the `data` blob at `offset` (in bytes) from the start, with `len` bytes.
    /// The caller guarantees `offset` and `len` are valid, and that the data at those is a valid UTF-8 string.
    /// NOTE: file stems may be empty, with both `offset` and `len` being zero.
    unsafe fn string_slice(data: &[u8], offset: StringOffset, len: ComponentStringLength) -> &str {
        debug_assert!(len > 0 || offset == 0);
        str::from_utf8_unchecked(Self::slice(data, offset, len as _))
    }

    /// Returns a subslice within the `data` blob at `offset` (in bytes) from the start, with `len` `T` elements.
    /// The caller guarantees `offset` and `len` are valid.
    unsafe fn slice<T>(data: &[u8], offset: u64, len: u64) -> &[T] {
        debug_assert!(offset + len * (mem::size_of::<T>() as u64) <= data.len() as _);

        slice::from_raw_parts(data.as_ptr().offset(offset as _) as *const _, len as _)
    }
}

/// (Reverse) iterator over the (folder) file path components starting at `path_component`.
struct FolderIter<'a, 'b> {
    reader: &'a FileTreeReader<'b>,
    path_component: Option<PathComponent>,
}

impl<'a, 'b> FolderIter<'a, 'b> {
    fn new(reader: &'a FileTreeReader<'b>, path_component: Option<PathComponent>) -> Self {
        Self {
            reader,
            path_component,
        }
    }
}

impl<'a, 'b> Iterator for FolderIter<'a, 'b> {
    type Item = &'a NonEmptyStr;

    fn next(&mut self) -> Option<Self::Item> {
        self.path_component.take().map(|path_component| {
            if let Some(parent) = path_component.parent {
                self.path_component
                    .replace(self.reader.path_component(parent));
            }
            // Folder names may not be empty.
            self.reader.non_empty_string(path_component.string)
        })
    }
}

#[cfg(test)]
mod tests {
    use {super::*, seahash::SeaHasher, std::hash::BuildHasher};

    struct BuildSeaHasher(SeaHasher);

    impl Default for BuildSeaHasher {
        fn default() -> Self {
            Self(SeaHasher::default())
        }
    }

    impl BuildHasher for BuildSeaHasher {
        type Hasher = SeaHasher;

        fn build_hasher(&self) -> Self::Hasher {
            self.0
        }
    }

    #[test]
    fn reader() {
        use minifilepath_macro::filepath;

        let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

        let paths = &[
            filepath!("foo/bar/baz"),
            filepath!("foo/bar/baz.cfg"),
            filepath!("foo/bar/baz.txt"),
            filepath!("foo/bar/.cfg"),
            filepath!("foo/bar/bill.txt"),
            filepath!("foo/bar/bob.cfg"),
            filepath!("fOO/bar/bill.txt"),
            filepath!("fOO/bar/bob.cfg"),
            filepath!("foo/bAr/bar"),
            filepath!("foo/bill.txt/bar"),
            filepath!("Bar"),
        ];

        let version = 7;

        let hashes = paths
            .iter()
            .map(|path| writer.insert(path).unwrap())
            .collect::<Vec<_>>();

        let len = writer.len();
        let string_len = writer.string_len();

        let data = writer.write_to_vec(version).unwrap().into_boxed_slice();

        let test_reader = |build_lookup: bool| {
            let reader = {
                let mut reader = FileTreeReader::new(&data).unwrap();

                if build_lookup {
                    reader.build_lookup();
                }

                reader
            };

            assert_eq!(reader.version(), version);
            assert_eq!(reader.len(), len);
            assert_eq!(reader.string_len(), string_len);

            let mut builder = FilePathBuilder::new();

            for (idx, hash) in hashes.iter().enumerate() {
                let result = reader.lookup_into(*hash, builder).unwrap();

                assert_eq!(paths[idx], result.as_file_path());

                builder = result.into_builder();
            }
        };

        test_reader(false);
        test_reader(true);
    }
}

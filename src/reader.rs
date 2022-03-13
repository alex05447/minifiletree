use {
    crate::*,
    minifilepath::{
        is_valid_path_component, FilePathBuf, FilePathBuilder, FilePathComponent,
        MAX_NUM_COMPONENTS,
    },
    ministr::NonEmptyStr,
    std::{
        collections::{HashMap, HashSet},
        iter::{ExactSizeIterator, Iterator},
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

            let lookup_keys = unsafe { Self::lookup_keys(self.data, lookup_len) };
            let lookup_values = unsafe { Self::lookup_values(self.data, lookup_len) };

            self.lookup.replace(
                lookup_keys
                    .iter()
                    .zip(lookup_values.iter())
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

    /// Returns the number of unique strings in the reader.
    pub fn num_strings(&self) -> usize {
        let header = unsafe { Self::header(self.data) };

        header.string_table_len() as _
    }

    /// Returns the total length in bytes of all unique strings in the reader.
    pub fn string_len(&self) -> usize {
        let header = unsafe { Self::header(self.data) };

        let string_section_start = Self::string_section_start(
            header.lookup_len(),
            header.path_components_len(),
            header.string_table_len(),
        );
        debug_assert!(string_section_start < self.data.len());

        let string_section_end = self.data.len();

        string_section_end - string_section_start
    }

    /// Returns a reverse (leaf to root) iterator over path [`components of the file path`](FilePathComponent) associated with the path `hash`, if any.
    pub fn lookup_iter(
        &self,
        hash: PathHash,
    ) -> Option<impl ExactSizeIterator<Item = FilePathComponent>> {
        let header = unsafe { Self::header(self.data) };

        self.lookup_leaf_path_component(header, hash)
            .map(|lpc| self.iter(header, lpc.path_component_index, lpc.num_components))
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

    // Attempts to validate the `data` to make sure it is a valid file tree blob, written by the `FileTreeWriter`.
    fn validate_blob(data: &[u8]) -> bool {
        // Check if the data is at least large enough to hold the smallest possible file tree blob.
        if data.len() < Self::min_size() {
            return false;
        }

        let header = unsafe { Self::header(data) };

        // Check the header magic.
        if !header.check_magic() {
            return false;
        }

        let lookup_len = header.lookup_len();
        let path_components_len = header.path_components_len();

        // Must have at least as many (or more) path components as there are lookup entries.
        if path_components_len < lookup_len {
            return false;
        }

        let string_table_len = header.string_table_len();

        // Must be large enough to accomodate the section lengths from the header.
        if data.len() < Self::required_size(lookup_len, path_components_len, string_table_len) {
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
        let path_components =
            unsafe { Self::path_components(data, lookup_len, path_components_len) };

        for path_component in path_components.iter().map(PackedPathComponent::unpack) {
            // Make sure all string indices are within the valid range.
            if path_component.string_index >= string_table_len {
                return false;
            }

            // Make sure all parent indices are within the valid range.
            if let Some(parent_index) = path_component.parent_index {
                if parent_index >= path_components_len {
                    return false;
                }
            }
        }

        // Assume the string table is valid.
        let string_table =
            unsafe { Self::string_table(data, lookup_len, path_components_len, string_table_len) };

        /*
                // All entries must be unique.
                #[cfg(debug_assertions)]
                if Self::has_duplicates_quadratic(string_table) {
                    return false;
                }
        */

        let string_section_start =
            Self::string_section_start(lookup_len, path_components_len, string_table_len);
        debug_assert!(string_section_start < data.len());

        let string_section_end = data.len();

        for string in string_table.iter().map(PackedInternedString::unpack) {
            // Make sure all string offsets and lengths in the string table are within the valid range.
            if string.offset < string_section_start as _ {
                return false;
            }

            if string.offset + string.len as StringOffset > string_section_end as StringOffset {
                return false;
            }

            // Make sure all strings are valid UTF-8.
            if let Ok(string) =
                str::from_utf8(unsafe { Self::slice(data, string.offset, string.len as _) })
            {
                // Make sure all strings are non-empty.
                if let Some(string) = NonEmptyStr::new(string) {
                    // Make sure all path components are valid.
                    if !is_valid_path_component(string) {
                        return false;
                    }
                } else {
                    return false;
                }
            } else {
                return false;
            }
        }

        // Assume the lookup values (leaf path components) are valid.
        let leaf_path_components = unsafe { Self::lookup_values(data, lookup_len) };

        /*
                // All entries must be unique.
                #[cfg(debug_assertions)]
                if Self::has_duplicates_quadratic(lookup_values) {
                    return false;
                }
        */

        let string_section_len = string_section_end - string_section_start;

        // Used to detect loops in the file path tree.
        let mut visited_path_components = HashSet::<PathComponentIndex>::new();

        for leaf_path_component in leaf_path_components
            .iter()
            .map(PackedLeafPathComponent::unpack)
        {
            // Make sure all path component indices are within the valid range.
            let path_component_index = leaf_path_component.path_component_index;

            if path_component_index >= path_components_len {
                return false;
            }

            let num_components = leaf_path_component.num_components;

            // Empty paths are invalid.
            if num_components == 0 {
                return false;
            }

            if num_components as usize > MAX_NUM_COMPONENTS {
                return false;
            }

            // Number of components for the path cannot be greater than the total number of unique components in the file tree.
            if num_components as u32 > path_components_len {
                return false;
            }

            let leaf_path_component_len = leaf_path_component.string_len;

            let num_separators = num_components - 1;
            let min_leaf_path_component_len = num_components + num_separators;

            // String length for the path cannot be less than the minimum (1 byte per component + separators).
            if leaf_path_component_len < min_leaf_path_component_len {
                return false;
            }

            // String length for the path (excluding the separators) cannot be greater than the total string section length.
            debug_assert!(leaf_path_component_len > num_separators);
            let leaf_path_component_len_without_separators =
                leaf_path_component_len - num_separators;

            if leaf_path_component_len_without_separators as usize > string_section_len {
                return false;
            }

            // Check for cycles starting at this leaf path component.
            {
                visited_path_components.clear();

                // Num components and string length obtained from iterating the path must match its declared properties.
                let mut actual_num_components: NumComponents = 1;
                let mut actual_len: FullStringLength = 0;

                let mut path_component_index = path_component_index;
                visited_path_components.insert(path_component_index);

                loop {
                    debug_assert!((path_component_index as usize) < path_components.len());
                    let path_component =
                        unsafe { path_components.get_unchecked(path_component_index as usize) }
                            .unpack();

                    let string_index = path_component.string_index;
                    debug_assert!(string_index < string_table_len);

                    let string =
                        unsafe { string_table.get_unchecked(string_index as usize) }.unpack();

                    // Count the separator character.
                    if actual_len != 0 {
                        actual_len += 1;
                    }

                    actual_len += string.len as FullStringLength;

                    // If the path component has a parent, keep processing.
                    if let Some(parent_index) = path_component.parent_index {
                        debug_assert!(parent_index < path_components_len);

                        // Cycles are not allowed.
                        if !visited_path_components.insert(parent_index) {
                            return false;
                        }

                        actual_num_components += 1;

                        path_component_index = parent_index;

                    // Otherwise we've reached the root of the path; time to check whether num components / string length match.
                    } else {
                        break;
                    }
                }

                if actual_num_components != num_components {
                    return false;
                }

                if actual_len != leaf_path_component_len {
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

            let lookup_keys = unsafe { Self::lookup_keys(self.data, lookup_len) };

            if let Some(idx) = lookup_keys
                .iter()
                .cloned()
                .map(u64_from_bin)
                .position(|key| key == hash)
            {
                let lookup_values = unsafe { Self::lookup_values(self.data, lookup_len) };
                debug_assert!(idx < lookup_values.len());
                Some(unsafe { lookup_values.get_unchecked(idx) }.unpack())
            } else {
                None
            }
        }
    }

    /// Clears and fills the `builder` with the full path for the `leaf_path_component`, using `/` as separators.
    fn build_path_string(
        &self,
        header: &FileTreeHeader,
        lpc: LeafPathComponent,
        builder: FilePathBuilder,
    ) -> FilePathBuf {
        let mut string = builder.into_inner();
        build_path_string(
            || self.iter(header, lpc.path_component_index, lpc.num_components),
            lpc.string_len,
            &mut string,
        );
        debug_assert!(!string.is_empty());
        unsafe { FilePathBuf::new_unchecked(string) }
    }

    /// The caller guarantees the path component `index` is valid;
    /// and that the path starting with `index` has exactly `num_components` components.
    fn iter(
        &self,
        header: &FileTreeHeader,
        index: PathComponentIndex,
        num_components: NumComponents,
    ) -> impl ExactSizeIterator<Item = FilePathComponent> {
        debug_assert!(index < header.path_components_len());

        PathIter::new(
            self,
            self.path_component_impl(header, index),
            num_components,
        )
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
    fn string_at_index(&self, index: StringIndex) -> FilePathComponent {
        self.string_at_offset_and_len(
            self.string_offset_and_len(unsafe { Self::header(self.data) }, index),
        )
    }

    /// The caller guarantees the string `index` is valid.
    fn string_offset_and_len(&self, header: &FileTreeHeader, index: StringIndex) -> InternedString {
        let string_table = unsafe {
            Self::string_table(
                self.data,
                header.lookup_len(),
                header.path_components_len(),
                header.string_table_len(),
            )
        };
        debug_assert!(index < string_table.len() as _);
        unsafe { string_table.get_unchecked(index as usize) }.unpack()
    }

    /// The caller guarantees `offset_and_len` is valid.
    fn string_at_offset_and_len(&self, offset_and_len: InternedString) -> FilePathComponent {
        unsafe { Self::string(self.data, offset_and_len.offset, offset_and_len.len) }
    }

    /// Calculates the size in bytes of the lookup keys array given the lookup length from the header.
    const fn lookup_keys_size(lookup_len: PathComponentIndex) -> usize {
        mem::size_of::<PathHash>() * lookup_len as usize
    }

    /// Calculates the size in bytes of the lookup values array given the lookup length from the header.
    const fn lookup_values_size(lookup_len: PathComponentIndex) -> usize {
        mem::size_of::<PackedLeafPathComponent>() * lookup_len as usize
    }

    /// Calculates the size in bytes of the path components array given its length from the header.
    const fn path_component_table_size(path_components_len: PathComponentIndex) -> usize {
        mem::size_of::<PackedPathComponent>() * path_components_len as usize
    }

    /// Calculates the size in bytes of the string table given its length from the header.
    const fn string_table_size(string_table_len: StringIndex) -> usize {
        mem::size_of::<PackedInternedString>() * string_table_len as usize
    }

    /// Minimum size of the (variable length) string section given the string table length. Assumes 1-byte strings.
    const fn min_string_section_size(string_table_len: StringIndex) -> usize {
        1 * string_table_len as usize
    }

    /// Minimum size of the valid file tree data blob.
    /// Header, 1 lookup entry, 1 path component entry, 1 string table entry, 1-byte string.
    fn min_size() -> usize {
        Self::required_size(1, 1, 1)
    }

    /// Calculates the required minimum data blob size in bytes for given section lengths from the header.
    fn required_size(
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
        string_table_len: StringIndex,
    ) -> usize {
        Self::string_section_start(lookup_len, path_components_len, string_table_len)
            + Self::min_string_section_size(string_table_len)
    }

    /// Calculates the offset in bytes to the (variable length) string section for given section lengths from the header.
    fn string_section_start(
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
        string_table_len: StringIndex,
    ) -> usize {
        mem::size_of::<FileTreeHeader>()
            + Self::lookup_keys_size(lookup_len)
            + Self::lookup_values_size(lookup_len)
            + Self::path_component_table_size(path_components_len)
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

    /// The caller guarantees the `data` is at least large enough to hold a `FileTreeHeader`.
    unsafe fn header(data: &[u8]) -> &FileTreeHeader {
        &*(data.as_ptr() as *const _)
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the array of lookup keys.
    const fn lookup_keys_offset() -> u64 {
        mem::size_of::<FileTreeHeader>() as _
    }

    /// Returns the subslice of lookup keys (path hashes) from the `data` blob.
    /// The caller guarantees `lookup_len` is valid for the `data` blob.
    unsafe fn lookup_keys<'d>(data: &'d [u8], lookup_len: PathComponentIndex) -> &'d [PathHash] {
        Self::slice(data, Self::lookup_keys_offset(), lookup_len as _)
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the array of lookup values.
    const fn lookup_values_offset(lookup_len: PathComponentIndex) -> u64 {
        Self::lookup_keys_offset() + (lookup_len as u64) * (mem::size_of::<PathHash>() as u64)
    }

    /// Returns the subslice of lookup values (leaf path components) from the `data` blob.
    /// The caller guarantees `lookup_len` is valid for the `data` blob.
    unsafe fn lookup_values<'d>(
        data: &'d [u8],
        lookup_len: PathComponentIndex,
    ) -> &'d [PackedLeafPathComponent] {
        Self::slice(
            data,
            Self::lookup_values_offset(lookup_len),
            lookup_len as _,
        )
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the array of path components.
    const fn path_components_offset(lookup_len: PathComponentIndex) -> u64 {
        Self::lookup_values_offset(lookup_len)
            + (lookup_len as u64) * (mem::size_of::<PackedLeafPathComponent>() as u64)
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

    /// Calculates the offset in bytes from the start of the file tree data blob to the string table.
    const fn string_table_offset(
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
    ) -> u64 {
        Self::path_components_offset(lookup_len)
            + (path_components_len as u64) * (mem::size_of::<PackedPathComponent>() as u64)
    }

    /// Returns the subslice of string table entries from the `data` blob.
    /// The caller guarantees `lookup_len`, `path_components_len` and `string_table_len` are valid for the `data` blob.
    unsafe fn string_table(
        data: &[u8],
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
        string_table_len: StringIndex,
    ) -> &[PackedInternedString] {
        Self::slice(
            data,
            Self::string_table_offset(lookup_len, path_components_len),
            string_table_len as _,
        )
    }

    /// Returns a non-empty UTF-8 string slice within the `data` blob at `offset` (in bytes) from the start, with `len` (>0) bytes.
    /// The caller guarantees `offset` and `len` are valid, and that the data at those is a valid UTF-8 string.
    unsafe fn string(
        data: &[u8],
        offset: StringOffset,
        len: ComponentStringLength,
    ) -> FilePathComponent {
        debug_assert!(len > 0);
        NonEmptyStr::new_unchecked(str::from_utf8_unchecked(Self::slice(
            data, offset, len as _,
        )))
    }

    /// Returns a subslice within the `data` blob at `offset` (in bytes) from the start, with `len` `T` elements.
    /// The caller guarantees `offset` and `len` are valid.
    unsafe fn slice<T>(data: &[u8], offset: u64, len: u64) -> &[T] {
        debug_assert!((offset as usize) < data.len());
        debug_assert!(((offset + len) as usize) <= data.len());

        slice::from_raw_parts(data.as_ptr().offset(offset as _) as *const _, len as _)
    }
}

/// (Reverse, leaf-to-root) iterator over the file path components starting at `cur_part`.
struct PathIter<'a, 'b> {
    reader: &'a FileTreeReader<'b>,
    cur_component: Option<PathComponent>,
    num_components: NumComponents,
}

impl<'a, 'b> PathIter<'a, 'b> {
    fn new(
        reader: &'a FileTreeReader<'b>,
        cur_part: PathComponent,
        num_components: NumComponents,
    ) -> Self {
        Self {
            reader,
            cur_component: Some(cur_part),
            num_components,
        }
    }
}

impl<'a, 'b> Iterator for PathIter<'a, 'b> {
    type Item = &'a NonEmptyStr;

    fn next(&mut self) -> Option<Self::Item> {
        self.cur_component.take().map(|cur_part| {
            let str = self.reader.string_at_index(cur_part.string_index);

            if let Some(parent_index) = cur_part.parent_index {
                self.cur_component
                    .replace(self.reader.path_component(parent_index));
            }

            debug_assert!(self.num_components > 0);
            self.num_components -= 1;

            str
        })
    }
}

impl<'a, 'b> ExactSizeIterator for PathIter<'a, 'b> {
    fn len(&self) -> usize {
        self.num_components as _
    }
}

#[cfg(test)]
mod tests {
    use {super::*, minifilepath::FilePath, seahash::SeaHasher, std::hash::BuildHasher};

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
            filepath!("foo/bar/baz.cfg"),
            filepath!("fOO/bar/bill.txt"),
            filepath!("foo/bAr/bar"),
            filepath!("Bar"),
        ];

        let version = 7;

        let hashes = paths
            .iter()
            .map(|path| writer.insert(path).unwrap())
            .collect::<Vec<_>>();

        let len = writer.len();
        let num_strings = writer.num_strings();
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
            assert_eq!(reader.num_strings(), num_strings);
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

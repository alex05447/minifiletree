use {
    crate::{
        util::*, FileTreeHeader, InternedString, PathHash, PathPart, PathPartIndex, StringIndex,
    },
    std::{
        iter::Iterator,
        mem::size_of,
        slice::from_raw_parts,
        str::{from_utf8, from_utf8_unchecked},
    },
};

/// Provides an API to lookup full file paths by their [`hashes`] in the data blob [`written`] by the [`FileTreeWriter`].
///
/// [`hashes`]: type.PathHash.html
/// [`written`]: struct.FileTreeWriter.html#method.write
/// [`FileTreeWriter`]: struct.FileTreeWriter.html
pub struct FileTreeReader<'a>(&'a [u8]);

impl<'a> FileTreeReader<'a> {
    /// Creates a [`FileTreeReader`] from the `data` blob [`written`] by the [`FileTreeWriter`].
    /// Attempts to validate the `data` blob and returns an error if `data` is not a valid file tree data blob.
    ///
    /// [`written`]: struct.FileTreeWriter.html#method.write
    /// [`FileTreeWriter`]: struct.FileTreeWriter.html
    pub fn new(data: &'a [u8]) -> Result<Self, ()> {
        if !Self::validate_blob(&data) {
            return Err(());
        }

        Ok(Self(data))
    }

    /// Creates a [`FileTreeReader`] from the `data` blob [`written`] by the [`FileTreeWriter`].
    ///
    /// # Safety
    /// Unsafe because no validation is performed of the `data` blob. The caller guarantees that `data` is a valid file tree data blob
    /// ([`is_valid`] returned `true` for it).
    ///
    /// [`written`]: struct.FileTreeWriter.html#method.write
    /// [`FileTreeWriter`]: struct.FileTreeWriter.html
    /// [`is_valid`]: #method.is_valid
    pub unsafe fn new_unchecked(data: &'a [u8]) -> Self {
        Self(data)
    }

    /// Returns `true` if `data` is a valid file tree data blob, [`written`] by the [`FileTreeWriter`].
    ///
    /// [`written`]: struct.FileTreeWriter.html#method.write
    /// [`FileTreeWriter`]: struct.FileTreeWriter.html
    pub fn is_valid(data: &'a [u8]) -> bool {
        Self::validate_blob(data)
    }

    /// Returns a reverse (leaf to root) iterator over path parts / components of the path associated with path `hash`, if any.
    pub fn lookup_iter(&self, hash: PathHash) -> Option<impl Iterator<Item = &'_ str>> {
        let header = unsafe { Self::header(self.0) };

        self.lookup_leaf_path_part(header, hash)
            .map(|path_part_index| self.iter(header, path_part_index))
    }

    /// Clears and fills the `string` with the full path associated with the path `hash`, if any, using '/' as separators, and returns `true`.
    /// Returns `false` and does not modify the `string` if there is no path associated with the `hash`.
    pub fn lookup_into(&self, hash: PathHash, string: &mut String) -> bool {
        let header = unsafe { Self::header(self.0) };

        self.lookup_leaf_path_part(header, hash)
            .map(|index| self.build_path_string(header, index, string))
            .is_some()
    }

    /// Returns a string with the full path associated with the path `hash`, if any.
    pub fn lookup(&self, hash: PathHash) -> Option<String> {
        let mut string = String::new();
        if self.lookup_into(hash, &mut string) {
            Some(string)
        } else {
            None
        }
    }

    // Attempts to validate the `data` to make sure it is a valid file tree blob, written by the `FileTreeWriter`.
    fn validate_blob(data: &[u8]) -> bool {
        // Check if the data is at least large enough to hold the smallest possible file tree blob.
        if data.len() < Self::min_size() {
            return false;
        }

        if data.len() > Self::max_size() {
            return false;
        }

        let header = unsafe { Self::header(data) };

        // Check the header magic.
        if !header.check_magic() {
            return false;
        }

        let lookup_len = header.lookup_len();
        let path_parts_len = header.path_parts_len();

        // Must have at least as many (or more) path parts as there are lookup entries.
        if path_parts_len < lookup_len {
            return false;
        }

        // Must have at least as many (or more) string table entries as there are lookup entries.
        let string_table_len = header.string_table_len();

        if string_table_len < lookup_len {
            return false;
        }

        // Must be large enough to accomodate the section lengths from the header.
        if data.len() < Self::required_size(lookup_len, path_parts_len, string_table_len) {
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

        // Assume the lookup values (path part indices) are valid.
        let lookup_values = unsafe { Self::lookup_values(data, lookup_len) };

        /*
               // All entries must be unique.
               #[cfg(debug_assertions)]
               if Self::has_duplicates_quadratic(lookup_values) {
                   return false;
               }
        */

        // Make sure all path part indices are within the valid range.
        for path_part_index in lookup_values.iter().cloned().map(u32_from_bin) {
            if path_part_index >= path_parts_len {
                return false;
            }
        }

        // Assume the path parts are valid.
        let path_parts = unsafe { Self::path_parts(data, lookup_len, path_parts_len) };

        for path_part in path_parts {
            // Make sure all path part string indices are within the valid range.
            if path_part.string_index() >= string_table_len {
                return false;
            }

            // Make sure all path part parent indices are within the valid range.
            if let Some(parent_index) = path_part.parent_index() {
                if parent_index >= path_parts_len {
                    return false;
                }
            }
        }

        // Assume the string table is valid.
        let string_table =
            unsafe { Self::string_table(data, lookup_len, path_parts_len, string_table_len) };

        /*
                // All entries must be unique.
                #[cfg(debug_assertions)]
                if Self::has_duplicates_quadratic(string_table) {
                    return false;
                }
        */

        let string_section_start =
            Self::string_section_start(lookup_len, path_parts_len, string_table_len);
        debug_assert!(string_section_start < data.len());

        let string_section_end = data.len();

        for string in string_table {
            // Make sure all string offsets and lengths in the string table are within the valid range.

            let offset = string.offset();

            if offset < string_section_start as u32 {
                return false;
            }

            let len = string.len();

            if offset + len > string_section_end as u32 {
                return false;
            }

            // Make sure all strings are valid UTF-8.
            if from_utf8(unsafe { Self::slice(data, offset, len) }).is_err() {
                return false;
            }
        }

        // Seems like all the offsets/lengths/indices in the blob are within valid ranges;
        // and all strings are valid UTF-8.
        // This at least guarantees all accesses to the data blob via the `FileTreeReader` will be memory-safe.

        true
    }

    /// Looks up the leaf path part index associated with path `hash`, if any.
    fn lookup_leaf_path_part(
        &self,
        header: &FileTreeHeader,
        hash: PathHash,
    ) -> Option<PathPartIndex> {
        let lookup_len = header.lookup_len();

        let lookup_keys = unsafe { Self::lookup_keys(self.0, lookup_len) };

        if let Some(idx) = lookup_keys
            .iter()
            .cloned()
            .map(u64_from_bin)
            .position(|key| key == hash)
        {
            let lookup_values = unsafe { Self::lookup_values(self.0, lookup_len) };
            debug_assert!(idx < lookup_values.len());
            Some(unsafe { *lookup_values.get_unchecked(idx) })
        } else {
            None
        }
    }

    /// Clears and fills the `string` with the full path for the path part `index`, using `/` as separators.
    /// The caller guarantees the path part `index` is valid.
    fn build_path_string(
        &self,
        header: &FileTreeHeader,
        index: PathPartIndex,
        string: &mut String,
    ) {
        build_path_string(|| self.iter(header, index), string);
    }

    /// The caller guarantees the path part `index` is valid.
    fn iter(&self, header: &FileTreeHeader, index: PathPartIndex) -> impl Iterator<Item = &'_ str> {
        debug_assert!(index < header.path_parts_len());

        PathIter {
            reader: self,
            cur_part: Some(self.path_part_impl(header, index)),
        }
    }

    /// The caller guarantees the path part `index` is valid.
    fn path_part(&self, index: PathPartIndex) -> PathPart {
        let header = unsafe { Self::header(self.0) };
        self.path_part_impl(header, index)
    }

    /// The caller guarantees the path part `index` is valid.
    fn path_part_impl(&self, header: &FileTreeHeader, index: PathPartIndex) -> PathPart {
        let path_parts =
            unsafe { Self::path_parts(self.0, header.lookup_len(), header.path_parts_len()) };
        debug_assert!(index < path_parts.len() as _);
        unsafe { *path_parts.get_unchecked(index as usize) }
    }

    /// The caller guarantees the string `index` is valid.
    fn string_at_index(&self, index: StringIndex) -> &str {
        self.string_at_offset_and_len(
            self.string_offset_and_len(unsafe { Self::header(self.0) }, index),
        )
    }

    /// The caller guarantees the string `index` is valid.
    fn string_offset_and_len(&self, header: &FileTreeHeader, index: StringIndex) -> InternedString {
        let string_table = unsafe {
            Self::string_table(
                self.0,
                header.lookup_len(),
                header.path_parts_len(),
                header.string_table_len(),
            )
        };
        debug_assert!(index < string_table.len() as _);
        unsafe { *string_table.get_unchecked(index as usize) }
    }

    fn string_at_offset_and_len(&self, offset_and_len: InternedString) -> &str {
        unsafe { Self::string(self.0, offset_and_len.offset(), offset_and_len.len()) }
    }

    /// Calculates the size in bytes of the lookup keys array given the lookup length from the header.
    const fn lookup_keys_size(lookup_len: u32) -> usize {
        size_of::<PathHash>() * lookup_len as usize
    }

    /// Calculates the size in bytes of the lookup values array given the lookup length from the header.
    const fn lookup_values_size(lookup_len: u32) -> usize {
        let mut size = size_of::<u32>() * lookup_len as usize;
        // Must be aligned to 8 bytes.
        size += size % 8;
        size
    }

    /// Calculates the size in bytes of the path parts array given its length from the header.
    const fn path_part_table_size(path_parts_len: u32) -> usize {
        size_of::<PathPart>() * path_parts_len as usize
    }

    /// Calculates the size in bytes of the string table given its length from the header.
    const fn string_table_size(string_table_len: u32) -> usize {
        size_of::<InternedString>() * string_table_len as usize
    }

    /// Minimum size of the (variable length) string section given the string table length. Assumes 1-byte strings.
    const fn string_section_size(string_table_len: u32) -> usize {
        1 * string_table_len as usize
    }

    /// Minimum size of the valid file tree data blob.
    /// Header, 1 lookup entry, 1 path part entry, 1 string table entry, 1-byte string.
    fn min_size() -> usize {
        Self::required_size(1, 1, 1)
    }

    /// Calculates the required minimum data blob size in bytes for given section lengths from the header.
    fn required_size(lookup_len: u32, path_parts_len: u32, string_table_len: u32) -> usize {
        Self::string_section_start(lookup_len, path_parts_len, string_table_len)
            + Self::string_section_size(string_table_len)
    }

    /// Calculates the offset in bytes to the (variable length) string section for given section lengths from the header.
    fn string_section_start(lookup_len: u32, path_parts_len: u32, string_table_len: u32) -> usize {
        size_of::<FileTreeHeader>()
            + Self::lookup_keys_size(lookup_len)
            + Self::lookup_values_size(lookup_len)
            + Self::path_part_table_size(path_parts_len)
            + Self::string_table_size(string_table_len)
    }

    /// Maximum size of the valid file tree data blob.
    const fn max_size() -> usize {
        u32::MAX as _
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
    const fn lookup_keys_offset() -> u32 {
        size_of::<FileTreeHeader>() as _
    }

    /// Returns the subslice of lookup keys (path hashes) from the `data` blob.
    /// The caller guarantees `lookup_len` is valid for the `data` blob.
    unsafe fn lookup_keys<'d>(data: &'d [u8], lookup_len: u32) -> &'d [PathHash] {
        Self::slice(data, Self::lookup_keys_offset(), lookup_len)
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the array of lookup values.
    const fn lookup_values_offset(lookup_len: u32) -> u32 {
        Self::lookup_keys_offset() + lookup_len * size_of::<PathHash>() as u32
    }

    /// Returns the subslice of lookup values (path part indices) from the `data` blob.
    /// The caller guarantees `lookup_len` is valid for the `data` blob.
    unsafe fn lookup_values<'d>(data: &'d [u8], lookup_len: u32) -> &'d [PathPartIndex] {
        Self::slice(data, Self::lookup_values_offset(lookup_len), lookup_len)
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the array of path parts.
    fn path_parts_offset(lookup_len: u32) -> u32 {
        let mut offset = Self::lookup_values_offset(lookup_len) + lookup_len * size_of::<PathPartIndex>() as u32;
        // Must be aligned to 8 bytes.
        offset += offset % 8;
        offset
    }

    /// Returns the subslice of path parts from the `data` blob.
    /// The caller guarantees `lookup_len` and `path_parts_len` are valid for the `data` blob.
    unsafe fn path_parts(data: &[u8], lookup_len: u32, path_parts_len: u32) -> &[PathPart] {
        Self::slice(data, Self::path_parts_offset(lookup_len), path_parts_len)
    }

    /// Calculates the offset in bytes from the start of the file tree data blob to the string table.
    fn string_table_offset(lookup_len: u32, path_parts_len: u32) -> u32 {
        Self::path_parts_offset(lookup_len) + path_parts_len * (size_of::<PathPart>() as u32)
    }

    /// Returns the subslice of string table entries from the `data` blob.
    /// The caller guarantees `lookup_len`, `path_parts_len` and `string_table_len` are valid for the `data` blob.
    unsafe fn string_table(
        data: &[u8],
        lookup_len: u32,
        path_parts_len: u32,
        string_table_len: u32,
    ) -> &[InternedString] {
        Self::slice(
            data,
            Self::string_table_offset(lookup_len, path_parts_len),
            string_table_len,
        )
    }

    /// Returns a UTF-8 string slice within the `data` blob at `offset` (in bytes) from the start, with `len` bytes.
    /// The caller guarantees `offset` and `len` are valid.
    unsafe fn string(data: &[u8], offset: u32, len: u32) -> &str {
        from_utf8_unchecked(Self::slice(data, offset, len))
    }

    /// Returns a subslice within the `data` blob at `offset` (in bytes) from the start, with `len` `T` elements.
    /// The caller guarantees `offset` and `len` are valid.
    unsafe fn slice<T>(data: &[u8], offset: u32, len: u32) -> &[T] {
        debug_assert!((offset as usize) < data.len());
        debug_assert!(((offset + len) as usize) <= data.len());

        from_raw_parts(data.as_ptr().offset(offset as _) as *const _, len as _)
    }
}

struct PathIter<'a, 'b> {
    reader: &'a FileTreeReader<'b>,
    cur_part: Option<PathPart>,
}

impl<'a, 'b> std::iter::Iterator for PathIter<'a, 'b> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(path_part) = self.cur_part.take() {
            let str = self.reader.string_at_index(path_part.string_index());

            if let Some(parent_index) = path_part.parent_index() {
                self.cur_part.replace(self.reader.path_part(parent_index));
            }

            Some(str)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::FileTreeWriter,
        seahash::SeaHasher,
        std::{hash::BuildHasher, path::Path},
    };

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
        let mut writer = FileTreeWriter::new(BuildSeaHasher::default());

        let paths = &["foo/bar/baz.cfg", "fOO/bar/bill.txt", "foo/bAr/bar", "Bar"];
        let lowercase_paths = paths
            .iter()
            .cloned()
            .map(str::to_lowercase)
            .collect::<Vec<_>>();

        let hashes = paths
            .iter()
            .map(|path| writer.insert(Path::new(path)).unwrap())
            .collect::<Vec<_>>();

        let mut data = Vec::new();
        writer.write(&mut data).unwrap();
        data.shrink_to_fit();
        let data = data.into_boxed_slice();

        let reader = FileTreeReader::new(&data).unwrap();

        let mut result = String::new();

        for hash in hashes {
            reader.lookup_into(hash, &mut result);

            assert!(lowercase_paths.contains(&result));
            assert!(paths
                .iter()
                .cloned()
                .find(|path| path.to_lowercase() == result)
                .is_some());
        }
    }
}

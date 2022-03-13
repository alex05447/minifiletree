use {
    crate::util::*,
    static_assertions::const_assert,
    std::{io::Write, num::NonZeroU32},
};

pub(crate) type PathComponentIndex = u32;
pub(crate) type StringIndex = u32;
pub(crate) type StringOffset = u64;

/// Maximum length in bytes of a single [`file path component`](minifilepath::FilePathComponent) string
/// is [`MAX_COMPONENT_LEN`](minifilepath::MAX_COMPONENT_LEN), which fits in a `u8`.
pub(crate) type ComponentStringLength = u8;

const_assert!((ComponentStringLength::MAX as usize) >= minifilepath::MAX_COMPONENT_LEN);

/// Maximum length in bytes of a valid [`path`](minifilepath::FilePath) (including separators)
/// is [`MAX_PATH_LEN`](minifilepath::MAX_PATH_LEN), which fits in a `u16`.
pub(crate) type FullStringLength = u16;

const_assert!((FullStringLength::MAX as usize) >= minifilepath::MAX_PATH_LEN);

/// Maximum number of components in a valid [`path`](minifilepath::FilePath)
/// is [`MAX_NUM_COMPONENTS`](minifilepath::MAX_NUM_COMPONENTS), which fits in a `u16`.
pub(crate) type NumComponents = u16;

const_assert!((NumComponents::MAX as usize) >= minifilepath::MAX_NUM_COMPONENTS);

const FILE_TREE_HEADER_MAGIC: u32 = 0x736b6170; // `paks`, little endian.

/// File tree data blob header.
///
/// File tree data blob layout:
///
/// | Header                    | `FileTreeHeader`              | 16b                           |
/// | Path hashes               | `[PathHash]`                  | 8b * `lookup_len`             |
/// | Leaf path components      | `[PackedLeafPathComponent]`   | 8b * `lookup_len`             |
/// | Path components           | `[PackedPathComponent]`       | 8b * `path_components_len`    |
/// | String table              | `[PackedInternedString]`      | 8b * `string_table_len`       |
/// | Strings                   | Contiguous UTF-8 string       | rest of the file              |
///
/// Fields are in whatever endianness we use; see `u32_from_bin()`.
#[repr(C, packed)]
pub(crate) struct FileTreeHeader {
    /// Arbitrary magic value for a quick sanity check.
    magic: u32,
    /// Length of the path lookup in elements
    /// (both the path hash array (keys) and the leaf path components array (values)).
    lookup_len: PathComponentIndex,
    /// Length of the path components array in elements.
    path_components_len: PathComponentIndex,
    /// Length of the string table in elements.
    string_table_len: StringIndex,
    /// Opaque user-provided "version" / user data information.
    version: u64,
}

impl FileTreeHeader {
    pub(crate) fn new(
        lookup_len: PathComponentIndex,
        path_components_len: PathComponentIndex,
        string_table_len: StringIndex,
        version: u64,
    ) -> Self {
        Self {
            magic: FILE_TREE_HEADER_MAGIC,
            lookup_len,
            path_components_len,
            string_table_len,
            version,
        }
    }

    pub(crate) fn check_magic(&self) -> bool {
        u32_from_bin(self.magic) == FILE_TREE_HEADER_MAGIC
    }

    pub(crate) fn lookup_len(&self) -> PathComponentIndex {
        u32_from_bin(self.lookup_len)
    }

    pub(crate) fn path_components_len(&self) -> PathComponentIndex {
        u32_from_bin(self.path_components_len)
    }

    pub(crate) fn string_table_len(&self) -> StringIndex {
        u32_from_bin(self.string_table_len)
    }

    pub(crate) fn version(&self) -> u64 {
        u64_from_bin(self.version)
    }

    pub(crate) fn write<W: Write>(&self, w: &mut W) -> Result<usize, std::io::Error> {
        let mut written = 0;

        // Magic.
        written += write_u32(w, FILE_TREE_HEADER_MAGIC)?;

        // Path lookup length.
        written += write_u32(w, self.lookup_len)?;

        // Path components length.
        written += write_u32(w, self.path_components_len)?;

        // String table length.
        written += write_u32(w, self.string_table_len)?;

        // Version.
        written += write_u64(w, self.version)?;

        debug_assert_eq!(written, std::mem::size_of::<Self>());

        Ok(written)
    }
}

/// Corresponds to a single leaf node of the file tree (i.e. a file).
///
/// Written to the file tree binary data blob as an element in the lookup table value array.
///
/// Fields are in whatever endianness we use; see `u32_from_bin()` / `u16_from_bin()`.
/// See `LeafPathComponent`.
#[derive(Clone, Copy)]
#[repr(C, packed)]
pub(crate) struct PackedLeafPathComponent {
    /// Index of the leaf path component in the path component array for this path.
    path_component_index: PathComponentIndex,
    /// Total number of components in this path. Non-null.
    /// Useful to have when building the file path string from the reverse iterator over the path components.
    num_components: NumComponents,
    /// Total length in bytes of the string for this path (including separators).
    /// Useful to have when building the file path string from the reverse iterator over the path components.
    string_len: FullStringLength,
}

impl PackedLeafPathComponent {
    pub(crate) fn unpack(&self) -> LeafPathComponent {
        LeafPathComponent::new(
            self.path_component_index(),
            self.num_components(),
            self.string_len(),
        )
    }

    fn path_component_index(&self) -> PathComponentIndex {
        u32_from_bin(self.path_component_index)
    }

    fn num_components(&self) -> NumComponents {
        u16_from_bin(self.num_components)
    }

    fn string_len(&self) -> FullStringLength {
        u16_from_bin(self.string_len)
    }
}

/// See `PackedLeafPathComponent`.
#[derive(Clone, Copy)]
pub(crate) struct LeafPathComponent {
    pub(crate) path_component_index: PathComponentIndex,
    pub(crate) num_components: NumComponents,
    pub(crate) string_len: FullStringLength,
}

impl LeafPathComponent {
    pub(crate) fn new(
        path_component_index: PathComponentIndex,
        num_components: NumComponents,
        string_len: FullStringLength,
    ) -> Self {
        Self {
            path_component_index,
            num_components,
            string_len,
        }
    }

    pub(crate) fn write<W: Write>(&self, w: &mut W) -> Result<usize, std::io::Error> {
        let mut written = 0;

        // Path component index.
        written += write_u32(w, self.path_component_index)?;

        // Num components.
        written += write_u16(w, self.num_components)?;

        // Total string length.
        written += write_u16(w, self.string_len)?;

        debug_assert_eq!(written, std::mem::size_of::<PackedLeafPathComponent>());

        Ok(written)
    }
}

/// Represents a unique component of a path (i.e. a unique file tree node).
///
/// Written to the file tree binary data blob as an element in the path component array section.
///
/// Fields are in whatever endianness we use; see `u32_from_bin()`.
/// See `PathComponent`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(C, packed)]
pub(crate) struct PackedPathComponent {
    /// Index of the path component's string in the string table / lookup array.
    string_index: StringIndex,
    /// (Optional) index of the parent path component in path components lookup array.
    /// `None` for root file tree elements, `Some` for non-root elements.
    /// Stored as an optional non-zero integer for space efficiency;
    /// decrement by one to get the actual lookup index.
    parent_index: Option<NonZeroU32>,
}

impl PackedPathComponent {
    pub(crate) fn unpack(&self) -> PathComponent {
        PathComponent::new(self.string_index(), self.parent_index())
    }

    fn string_index(&self) -> StringIndex {
        u32_from_bin(self.string_index)
    }

    /// NOTE - this does the `-1` subtraction.
    fn parent_index(&self) -> Option<PathComponentIndex> {
        self.parent_index
            .map(NonZeroU32::get)
            .map(u32_from_bin)
            .map(|x| x - 1)
    }
}

/// See `PackedPathComponent`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct PathComponent {
    pub(crate) string_index: StringIndex,
    pub(crate) parent_index: Option<PathComponentIndex>,
}

impl PathComponent {
    pub(crate) fn new(string_index: StringIndex, parent_index: Option<PathComponentIndex>) -> Self {
        Self {
            string_index,
            parent_index,
        }
    }

    pub(crate) fn write<W: Write>(&self, w: &mut W) -> Result<usize, std::io::Error> {
        let mut written = 0;

        // String index.
        written += write_u32(w, self.string_index)?;

        // Parent index.
        written += write_u32(
            w,
            self.parent_index
                .map(|parent_index| parent_index + 1)
                .unwrap_or(0),
        )?;

        debug_assert_eq!(written, std::mem::size_of::<PackedPathComponent>());

        Ok(written)
    }
}

/// Offset and (non-null) length in bytes of a unique string in the string section
/// (either w.r.t. the string section itself, when writing, or w.r.t. the full data blob, when reading).
/// Each string represents a unique [`file path component`](minifilepath::FilePathComponent).
///
/// Written to the file tree binary data blob as an element in the string table / lookup array section.
///
/// Fields are in whatever endianness we use; see `u64_from_bin()`.
/// See `InternedString`.
#[derive(Clone, Copy)]
#[repr(C, packed)]
pub(crate) struct PackedInternedString {
    /// Packed offset in bytes to the start of the string and its length in bytes.
    ///
    /// Highest byte: string length, lower bytes: offset to string.
    offset_and_len: u64,
}

impl PackedInternedString {
    pub(crate) fn unpack(&self) -> InternedString {
        let (offset, len) = self.offset_and_len();

        InternedString::new(offset, len)
    }

    fn offset_and_len(&self) -> (StringOffset, ComponentStringLength) {
        Self::unpack_offset_and_len(u64_from_bin(self.offset_and_len))
    }

    // See `pack_offset_and_len`.
    fn unpack_offset_and_len(offset_and_len: u64) -> (StringOffset, ComponentStringLength) {
        (
            offset_and_len & 0x00ff_ffff_ffff_ffffu64,
            ((offset_and_len & 0xff00_0000_0000_0000u64) >> 56) as ComponentStringLength,
        )
    }
}

/// See `PackedInternedString`.
#[derive(Clone, Copy)]
pub(crate) struct InternedString {
    pub(crate) offset: StringOffset,
    pub(crate) len: ComponentStringLength,
}

impl InternedString {
    pub(crate) fn new(offset: StringOffset, len: ComponentStringLength) -> Self {
        Self { offset, len }
    }

    pub(crate) fn write<W: Write>(&self, w: &mut W, offset: u64) -> Result<usize, std::io::Error> {
        let mut written = 0;

        let new_offset_and_len = Self::pack_offset_and_len(self.offset + offset, self.len);

        // Offset and length.
        written += write_u64(w, new_offset_and_len)?;

        debug_assert_eq!(written, std::mem::size_of::<PackedInternedString>());

        Ok(written)
    }

    // See `unpack_offset_and_len`.
    fn pack_offset_and_len(offset: StringOffset, len: ComponentStringLength) -> u64 {
        // Maximum `offset` value we can encode is 56 bits, or 64 petabytes, which is more than enough.
        debug_assert!(offset < 0x00ff_ffff_ffff_ffffu64);

        (((len as u64) << 56) & 0xff00_0000_0000_0000u64) | (offset & 0x00ff_ffff_ffff_ffffu64)
    }
}

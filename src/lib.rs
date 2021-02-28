//!
//! A small helper library to gather collections of lowercase UTF-8 string file paths, associate them with unique hashes,
//! and store them space-efficiently in a binary data blob;
//! for it to be later serialized/deserialized and used to efficiently look up the full string paths by their hashes.
//!

mod error;
mod reader;
mod util;
mod writer;

pub use error::*;
pub use reader::*;
pub use writer::*;

use {
    crate::util::*,
    std::{io::Write, num::NonZeroU32},
};

/// Type alias for a hash of a path - simply the output of the user-provided [`Hasher`] for a path,
/// processed root to leaf, converted to lowercase, and skipping the path separators.
///
/// [`Hasher`]: std::hash::Hasher
pub type PathHash = u64;

pub(crate) type PathPartIndex = u32;
type StringIndex = u32;
type StringOffset = u32;
type StringLength = u32;

/// Offset and length in bytes of a unique string in the string section
/// (either w.r.t. the string section itself, when writing, or w.r.t. the full data blob, when reading).
///
/// Written to the file tree binary data blob as an element in the string lookup array section.
/// Fields are in whatever endianness we use; see `u32_from_bin()`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(C, packed)]
struct InternedString {
    offset: StringOffset,
    /// String length in bytes.
    len: StringLength,
}

impl InternedString {
    fn offset(&self) -> StringOffset {
        u32_from_bin(self.offset)
    }

    fn len(&self) -> StringLength {
        u32_from_bin(self.len)
    }
}

/// Represents a unique part / component of a path (i.e. a unique file tree node).
///
/// Written to the file tree binary data blob as an element in the path part array section.
/// Fields are in whatever endianness we use; see `u32_from_bin()`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C, packed)]
struct PathPart {
    /// Index of the path part's string in the string lookup array.
    string_index: StringIndex,
    /// (Optional) index of the parent path part in path parts lookup array.
    /// `None` for root file tree elements, `Some` for non-root elements.
    /// Stored as an optional non-zero integer for space efficiency;
    /// decrement by one to get the actual lookup index.
    parent_index: Option<NonZeroU32>,
}

impl PathPart {
    fn string_index(&self) -> StringIndex {
        u32_from_bin(self.string_index)
    }

    /// NOTE - this does the `-1` subtraction.
    fn parent_index(&self) -> Option<PathPartIndex> {
        self.parent_index
            .map(|parent_index| u32_from_bin(parent_index.get()) - 1)
    }
}

const FILE_TREE_HEADER_MAGIC: u32 = 0x736b6170; // `paks`, little endian.

/// File tree data blob header.
///
/// Fields are in whatever endianness we use; see `u32_from_bin()`.
#[repr(C, packed)]
struct FileTreeHeader {
    /// Arbitrary magic value for a quick sanity check.
    magic: u32,
    /// Length of the path lookup.
    lookup_len: u32,
    /// Length of the path parts array in elements.
    path_parts_len: u32,
    /// Length of the string table in elements.
    string_table_len: u32,
}

impl FileTreeHeader {
    fn check_magic(&self) -> bool {
        u32_from_bin(self.magic) == FILE_TREE_HEADER_MAGIC
    }

    fn lookup_len(&self) -> u32 {
        u32_from_bin(self.lookup_len)
    }

    fn path_parts_len(&self) -> u32 {
        u32_from_bin(self.path_parts_len)
    }

    fn string_table_len(&self) -> u32 {
        u32_from_bin(self.string_table_len)
    }

    fn write<W: Write>(
        w: &mut W,
        lookup_len: u32,
        path_parts_len: u32,
        string_table_len: u32,
    ) -> Result<usize, std::io::Error> {
        let mut written = 0;

        // Magic.
        written += w.write(&u32_to_bin_bytes(FILE_TREE_HEADER_MAGIC))?;

        // Path lookup length.
        written += w.write(&u32_to_bin_bytes(lookup_len))?;

        // Path parts length.
        written += w.write(&u32_to_bin_bytes(path_parts_len))?;

        // String table length.
        written += w.write(&u32_to_bin_bytes(string_table_len))?;

        Ok(written)
    }
}

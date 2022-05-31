//!
//! A small helper Rust library to gather collections of UTF-8 relative file paths, associate them with unique hashes,
//! and store them space-efficiently in a binary data blob;
//! for it to be later serialized/deserialized and used to efficiently look up the string paths by their hashes.
//!
//! Used data structure is an inverted directory/file tree, with leaf nodes (i.e. files) indexed by the path hashes
//! and referencing their parent nodes (i.e. folders) recursively.
//!
//! Path component (and also file name extension) strings are deduplicated, as are the file tree nodes.
//!
//! Lookup results may be returned as a (reverse) iterator over the path components (including the extension),
//! or as an owned [`file path buffer`](minifilepath::FilePathBuf).

mod data;
mod error;
mod reader;
mod util;
mod writer;

pub(crate) use {data::*, util::*};
pub use {error::*, reader::*, writer::*};

/// Type alias for a hash of a [`file path`](minifilepath::FilePath) - simply the output of the user-provided [`std::hash::Hasher`]
/// for path [`components`](minifilepath::FilePath#method.components), root to leaf (skipping the separators).
pub type PathHash = u64;

/// Type alias for a user-provided "version" value stored to the file tree data blob when [`writing`](Writer::write) it.
pub type Version = u64;

use minifilepath::FilePathComponent;

/// The file name component of the [`looked up`](Reader::lookup_iter) [`file path`](minifilepath::FilePath).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FileName<'a> {
    /// File name path component with an extension (e.g. "bar.txt" in "foo/bar.txt", ".gitignore" in "foo/.gitignore").
    WithExtension {
        /// Extension part of the file name path component with an extension (e.g. "txt" in "foo/bar.txt", "gitignore" in "foo/.gitignore").
        extension: FilePathComponent<'a>,
        /// File stem part of the file name path component with an extension (e.g. "bar" in "foo/bar.txt", None in "foo/.gitignore").
        file_stem: Option<FilePathComponent<'a>>,
    },
    /// File name path component with no extension (e.g. "bar" in "foo/bar").
    NoExtension(FilePathComponent<'a>),
}

/// Result of a [`file path`](minifilepath::FilePath) [`look up`](Reader::lookup_iter) in the [`Reader`].
///
/// E.g.: `FilePathIter{ file_name: FileName::WithExtension{ extension: "txt", file_stem: "baz" }, file_path: ["bar", "foo"] }`
/// for `"foo/bar/baz.txt"`.
pub struct FilePathIter<'a, T> {
    /// File name component of the looked up file path.
    ///
    /// E.g.: `FileName::WithExtension{ extension: "txt", file_stem: "bar" }` for `"foo/bar.txt"`,
    /// `FileName::WithExtension{ extension: ".gitignore", file_stem: None }` for `"foo/bar/.gitignore"`,
    /// `FileName::NoExtension("bar")` for `"foo/bar"`.
    pub file_name: FileName<'a>,
    /// A (reverse) iterator over the components (i.e. folder names) of the "file path" part of the looked up file path.
    ///
    /// E.g.: `["foo"]` for `"foo/bar.txt"`,
    /// `["bar", "foo"]` for `"foo/bar/.gitignore"`.
    pub file_path: T,
}

impl<'a, T: Iterator<Item = FilePathComponent<'a>>> FilePathIter<'a, T> {
    pub(crate) fn eq<'u, U: Iterator<Item = FilePathComponent<'u>>>(
        self,
        other: FilePathIter<'u, U>,
    ) -> bool {
        self.file_name == other.file_name && self.file_path.eq(other.file_path)
    }
}

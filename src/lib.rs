//!
//! A small helper library to gather collections of UTF-8 relative file paths, associate them with unique hashes,
//! and store them space-efficiently in a binary data blob;
//! for it to be later serialized/deserialized and used to efficiently look up the string paths by their hashes.
//!

mod data;
mod error;
mod reader;
mod util;
mod writer;

pub(crate) use {data::*, util::*};
pub use {error::*, reader::*, writer::*};

/// Type alias for a hash of a [`path`](minifilepath::FilePath) - simply the output of the user-provided [`std::hash::Hasher`]
/// for path [`components`](minifilepath::FilePath#method.components), root to leaf (skipping the separators).
pub type PathHash = u64;

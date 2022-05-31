use {
    crate::*,
    minifilepath::FilePathBuf,
    std::{
        error::Error,
        fmt::{Display, Formatter},
    },
};

/// An error returned by the [`Writer`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum WriterError {
    /// A file was already inserted at this path.
    PathAlreadyExists,
    /// A folder was already inserted at this file path
    /// (and we cannot have a folder and a file with the same name at the same path).
    ///
    /// E.g.: insert `"foo/bar/baz"`, where `"bar"` is a folder, followed by `"foo/bar"`, where `"bar"` is a file.
    FolderAlreadyExistsAtFilePath,
    /// A file was already inserted at a folder path.
    /// Contains the path to the existing file.
    ///
    /// E.g.: insert `"foo/bar"`, where `"bar"` is a file, followed by `"foo/bar/baz"`, where "bar" is a folder.
    /// `"foo/bar"` is the returned path to the existing file.
    FileAlreadyExistsAtFolderPath(FilePathBuf),
    /// Path hash collides with an existing file path.
    /// Contains the path to the existing file.
    PathHashCollision(FilePathBuf),
}

impl Error for WriterError {}

impl Display for WriterError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use WriterError::*;

        match self {
            PathAlreadyExists => "a file was already inserted at this path".fmt(f),
            FolderAlreadyExistsAtFilePath => "a folder was already inserted at this path".fmt(f),
            FileAlreadyExistsAtFolderPath(path) => {
                write!(f, "a file was already inserted at folder path \"{}\"", path)
            }
            PathHashCollision(existing) => write!(
                f,
                "path hash collides with existing file path \"{}\"",
                existing
            ),
        }
    }
}

/// An error returned by the [`Reader`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ReaderError {
    /// The file tree data has an unexpected declared version.
    /// Contains the found version value.
    UnexpectedVersion(Version),
    /// The file tree data blob is invalid or corrupted.
    InvalidData,
}

impl Error for ReaderError {}

impl Display for ReaderError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use ReaderError::*;

        match self {
            UnexpectedVersion(version) => write!(
                f,
                "the file tree data has an unexpected version value ({})",
                version
            ),
            InvalidData => "the file tree data blob is invalid or corrupted".fmt(f),
        }
    }
}

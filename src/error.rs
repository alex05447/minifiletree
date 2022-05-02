use {
    minifilepath::FilePathBuf,
    std::{
        error::Error,
        fmt::{Display, Formatter},
    },
};

/// An error returned by the [`file tree writer`](struct.FileTreeWriter.html).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FileTreeWriterError {
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

impl Error for FileTreeWriterError {}

impl Display for FileTreeWriterError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use FileTreeWriterError::*;

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

use {
    minifilepath::FilePathBuf,
    std::{
        error::Error,
        fmt::{Display, Formatter},
    },
};

/// An error returned by the [`file tree writer`].
///
/// [`file tree writer`]: struct.FileTreeWriter.html
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FileTreeWriterError {
    /// A file or folder was already inserted at this file path.
    /// Contains the path to the exisiting file or folder.
    FileOrFolderAlreadyExistsAtFilePath(FilePathBuf),
    /// A file was already inserted at this file or folder path.
    /// Contains the path to the existing file.
    FileAlreadyExistsAtFileOrFolderPath(FilePathBuf),
    /// Path hash collides with an existing file path.
    /// Contains the path to the existing file.
    PathHashCollision(FilePathBuf),
}

impl Error for FileTreeWriterError {}

impl Display for FileTreeWriterError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use FileTreeWriterError::*;

        match self {
            FileOrFolderAlreadyExistsAtFilePath(path) => write!(
                f,
                "a file or folder was already inserted at file path \"{}\"",
                path
            ),
            FileAlreadyExistsAtFileOrFolderPath(path) => write!(
                f,
                "a file was already inserted at file or folder path \"{}\"",
                path
            ),
            PathHashCollision(existing) => write!(
                f,
                "path hash collides with existing file path \"{}\"",
                existing
            ),
        }
    }
}

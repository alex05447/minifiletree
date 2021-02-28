use std::{
    error::Error,
    fmt::{Display, Formatter},
    path::PathBuf,
};

/// An error returned by the [`file tree writer`].
///
/// [`file tree writer`]: struct.FileTreeWriter.html
#[derive(Debug)]
pub enum FileTreeWriterError {
    /// Empty paths are not allowed.
    EmptyPath,
    /// A path component contains invalid UTF-8.
    /// Contains the path to the invalid component.
    InvalidUTF8(PathBuf),
    /// A path component is empty.
    /// Contains the path to the empty component.
    EmptyPathComponent(PathBuf),
    /// Paths with prefixes are not allowed.
    PrefixedPath,
    /// Path contains an invalid component (root, current or parent directory).
    /// Contains the path to the invalid component.
    InvalidPathComponent(PathBuf),
    /// A file or folder was already inserted at this file path.
    /// Contains the path to the exisiting file or folder.
    FileOrFolderAlreadyExistsAtFilePath(PathBuf),
    /// A file was already inserted at this file or folder path.
    /// Contains the path to the existing file.
    FileAlreadyExistsAtFileOrFolderPath(PathBuf),
    /// Path hash collides with an existing file path.
    /// Contains the path to the existing file.
    PathHashCollision(PathBuf),
}

impl Error for FileTreeWriterError {}

impl Display for FileTreeWriterError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use FileTreeWriterError::*;

        match self {
            EmptyPath => "empty paths are not allowed".fmt(f),
            InvalidUTF8(path) => write!(f, "a path component at \"{:?}\" contains invalid UTF-8", path),
            EmptyPathComponent(path) => write!(f, "a path component at \"{:?}\" is empty", path),
            PrefixedPath => "paths with prefixes are not allowed".fmt(f),
            InvalidPathComponent(path) => write!(f, "path contains an invalid component at \"{:?}\" (root, current or parent directory)", path),
            FileOrFolderAlreadyExistsAtFilePath(path) => write!(f, "a file or folder was already inserted at file path \"{:?}\"", path),
            FileAlreadyExistsAtFileOrFolderPath(path) => write!(f, "a file was already inserted at file or folder path \"{:?}\"", path),
            PathHashCollision(existing) => write!(f, "path hash collides with existing file path \"{:?}\"", existing),
        }
    }
}

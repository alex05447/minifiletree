use {
    minifilepath::*,
    minifiletree::*,
    seahash::*,
    std::{env, ffi::OsStr, fs, hash::BuildHasher, io, path::PathBuf},
};

#[derive(Default)]
struct BuildSeaHasher;

impl BuildHasher for BuildSeaHasher {
    type Hasher = SeaHasher;

    fn build_hasher(&self) -> Self::Hasher {
        SeaHasher::new()
    }
}

fn into_io_error<E>(err: E) -> io::Error
where
    E: Into<Box<dyn std::error::Error + Send + Sync>>,
{
    io::Error::new(io::ErrorKind::Other, err)
}

/// Call `f` for each file in the directory at `dir_path`, recursively,
/// passing it the relative `FilePath` w.r.t. `dir_path`.
fn iterate_files_in_dir<F: FnMut(&FilePath) -> Result<(), io::Error>>(
    dir_path: &mut PathBuf,
    f: &mut F,
) -> Result<(), std::io::Error> {
    iterate_files_in_dir_impl(dir_path, FilePathBuilder::new(), f).map(|_| ())
}

fn iterate_files_in_dir_impl<F: FnMut(&FilePath) -> Result<(), io::Error>>(
    dir_path: &mut PathBuf,
    mut relative_path: FilePathBuilder,
    f: &mut F,
) -> Result<FilePathBuilder, std::io::Error> {
    for entry in fs::read_dir(&dir_path)? {
        let entry = entry?;
        let name = entry.file_name();
        let is_file = entry.file_type()?.is_file();

        relative_path = iterate_dir_entry(&name, is_file, dir_path, relative_path, f)?;
    }

    Ok(relative_path)
}

fn iterate_dir_entry<F: FnMut(&FilePath) -> Result<(), io::Error>>(
    name: &OsStr,
    is_file: bool,
    full_path: &mut PathBuf,
    mut relative_path: FilePathBuilder,
    f: &mut F,
) -> Result<FilePathBuilder, io::Error> {
    full_path.push(&name);
    relative_path.push(&name).map_err(into_io_error)?;

    if is_file {
        relative_path = {
            let relative_path = relative_path
                .build()
                .ok_or(into_io_error("empty file path"))?;

            f(&relative_path)?;

            relative_path.into_builder()
        };
    } else {
        relative_path = iterate_files_in_dir_impl(full_path, relative_path, f)?;
    }

    full_path.pop();
    relative_path.pop();

    Ok(relative_path)
}

fn main() -> Result<(), io::Error> {
    // "... minifiletree"
    let root_dir = env::current_dir()?;
    // "... minifiletree/target"
    let mut target_dir = root_dir;
    target_dir.push("target");

    println!("Processing files in {:?}", target_dir);

    // Iterate the files in the target directory, recursively,
    // insert them into the writer and collect the hashes.

    let mut hashes = Vec::new();
    let mut writer = FileTreeWriter::new(BuildSeaHasher);

    iterate_files_in_dir(&mut target_dir, &mut |relative_path| {
        hashes.push(writer.insert(relative_path).map_err(into_io_error)?);
        Ok(())
    })?;

    let num_paths = writer.len();
    let num_strings = writer.num_strings();
    let string_len = writer.string_len();
    let num_components = writer.num_components();
    let num_extensions = writer.num_extensions();

    // Serialize the written paths to the data blob.

    let version = 7;

    let blob = writer.write_to_vec(version)?;

    println!(
        "Wrote {} paths, {} unique strings ({}b), {} components, {} extensions, {}b total:",
        num_paths,
        num_strings,
        string_len,
        num_components,
        num_extensions,
        blob.len()
    );

    // Read the blob, lookup the paths using the collected hashes.

    let reader = {
        let mut reader = Reader::new(&blob, Some(version))
            .map_err(|_| into_io_error("failed to read the filetree blob"))?;

        reader.build_lookup();

        reader
    };

    let mut path = FilePathBuilder::new();

    for (idx, hash) in hashes.iter().enumerate() {
        path = {
            let path = reader.lookup_into(*hash, path).unwrap();
            println!("{}: {}", idx, path);
            path.into_builder()
        }
    }

    Ok(())
}

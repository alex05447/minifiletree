use {
    crate::*,
    std::{io::Write, iter::Iterator, mem},
};

pub(crate) fn u16_to_bin_bytes(val: u16) -> [u8; 2] {
    if cfg!(feature = "big_endian") {
        u16::to_be_bytes(val)
    } else {
        u16::to_le_bytes(val)
    }
}

pub(crate) fn u16_from_bin(bin: u16) -> u16 {
    if cfg!(feature = "big_endian") {
        u16::from_be(bin)
    } else {
        u16::from_le(bin)
    }
}

pub(crate) fn u32_to_bin_bytes(val: u32) -> [u8; 4] {
    if cfg!(feature = "big_endian") {
        u32::to_be_bytes(val)
    } else {
        u32::to_le_bytes(val)
    }
}

pub(crate) fn u32_from_bin(bin: u32) -> u32 {
    if cfg!(feature = "big_endian") {
        u32::from_be(bin)
    } else {
        u32::from_le(bin)
    }
}

pub(crate) fn u64_to_bin_bytes(val: u64) -> [u8; mem::size_of::<u64>()] {
    if cfg!(feature = "big_endian") {
        u64::to_be_bytes(val)
    } else {
        u64::to_le_bytes(val)
    }
}

pub(crate) fn u64_from_bin(bin: u64) -> u64 {
    if cfg!(feature = "big_endian") {
        u64::from_be(bin)
    } else {
        u64::from_le(bin)
    }
}

fn write_all<W: Write>(w: &mut W, buf: &[u8]) -> Result<usize, std::io::Error> {
    w.write_all(buf).map(|_| buf.len())
}

pub(crate) fn write_u64<W: Write>(w: &mut W, val: u64) -> Result<usize, std::io::Error> {
    write_all(w, &u64_to_bin_bytes(val))
}

pub(crate) fn write_u32<W: Write>(w: &mut W, val: u32) -> Result<usize, std::io::Error> {
    write_all(w, &u32_to_bin_bytes(val))
}

pub(crate) fn write_u16<W: Write>(w: &mut W, val: u16) -> Result<usize, std::io::Error> {
    write_all(w, &u16_to_bin_bytes(val))
}

/// Takes a file path iterator and known full path string length `len`,
/// clears and fills the `string` with the full path, using `/` as separators.
///
/// The caller guarantees the string built from the iterator (including the separators) is actually going to be `len` bytes long.
pub(crate) fn build_path_string<'i, I>(
    iter: FilePathIter<'i, I>,
    len: FullStringLength,
    string: &mut String,
) where
    I: Iterator<Item = FilePathComponent<'i>>,
{
    string.clear();
    string.reserve(len as _);

    let string = unsafe { string.as_mut_vec() };
    unsafe { string.set_len(len as _) };

    // "f  o  o  /  b  a  r  /  b  a  z  .  c  f  g" len = 15
    //  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14

    let mut offset = len;

    let mut copy_str = |s: &str| {
        let str_len = s.len() as FullStringLength;
        debug_assert!(
            offset >= str_len,
            "provided and calculated string lengths mismatch"
        );
        offset -= str_len;

        unsafe {
            std::ptr::copy_nonoverlapping(
                s.as_ptr(),
                string.as_mut_ptr().offset(offset as _),
                s.len(),
            )
        };
    };

    match iter.file_name {
        FileName::WithExtension {
            extension,
            file_stem,
        } => {
            copy_str(extension);
            copy_str(".");

            if let Some(file_stem) = file_stem {
                copy_str(file_stem);
            }
        }
        FileName::NoExtension(file_name) => {
            copy_str(file_name);
        }
    }

    for component in iter.file_path {
        copy_str("/");
        copy_str(component);
    }

    debug_assert_eq!(offset, 0);
}

pub(crate) fn debug_unreachable() -> ! {
    if cfg!(debug_assertions) {
        unreachable!()
    } else {
        unsafe { std::hint::unreachable_unchecked() }
    }
}

pub(crate) unsafe fn debug_unwrap<T>(val: Option<T>) -> T {
    if let Some(val) = val {
        val
    } else {
        debug_unreachable()
    }
}

use {
    crate::*,
    std::{
        collections::{hash_map::Entry, HashMap},
        hash::Hash,
        io::Write,
        iter::Iterator,
        mem, slice,
    },
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

/// One or multiple values in the multimap associated with a given key.
enum OneOrMultiple<T> {
    /// Usual case - one value associated with a key.
    One(T),
    /// Rare hash collision case - multiple values associated with a key.
    Multiple(Vec<T>),
}

/// A simple multimap optimized for the usual case of 1 value per key with no overhead,
/// but which does support multiple values by storing them in a `Vec` when necessary.
/// Only supports `insert()` and `get()` methods.
pub(crate) struct MultiMap<K: Eq + Hash, V: Eq + Copy>(HashMap<K, OneOrMultiple<V>>);

impl<K: Eq + Hash, V: Eq + Copy> MultiMap<K, V> {
    pub(crate) fn new() -> Self {
        Self(HashMap::new())
    }

    /// The caller guarantees that `value` is not associated with `key`.
    pub(crate) fn insert(&mut self, key: K, value: V) {
        match self.0.entry(key) {
            Entry::Occupied(mut entry) => {
                let entry = entry.get_mut();
                match entry {
                    OneOrMultiple::One(existing) => {
                        debug_assert!(*existing != value);
                        *entry = OneOrMultiple::Multiple(vec![*existing, value]);
                    }
                    OneOrMultiple::Multiple(existing) => {
                        debug_assert!(!existing.contains(&value));
                        existing.push(value);
                    }
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(OneOrMultiple::One(value));
            }
        }
    }

    pub(crate) fn get(&self, key: &K) -> Option<&[V]> {
        self.0.get(&key).map(|entry| match entry {
            OneOrMultiple::One(value) => slice::from_ref(value),
            OneOrMultiple::Multiple(values) => values,
        })
    }

    /// Returns an iterator over entries in the multimap associated with `key` in unspecified order.
    pub(crate) fn get_iter(&self, key: &K) -> impl Iterator<Item = &V> {
        MultiMapIter(self.get(&key).map(<[V]>::iter))
    }

    pub(crate) fn get_mut(&mut self, key: &K) -> Option<&mut [V]> {
        self.0.get_mut(&key).map(|entry| match entry {
            OneOrMultiple::One(value) => slice::from_mut(value),
            OneOrMultiple::Multiple(values) => values,
        })
    }

    /// Returns an iterator over entries in the multimap associated with `key` in unspecified order.
    pub(crate) fn get_iter_mut(&mut self, key: &K) -> impl Iterator<Item = &mut V> {
        MultiMapIterMut(self.get_mut(&key).map(<[V]>::iter_mut))
    }

    pub(crate) fn clear(&mut self) {
        self.0.clear()
    }

    /// Returns an iterator over all entries in the multimap in unspecified order.
    #[cfg(test)]
    pub(crate) fn iter(&self) -> impl Iterator<Item = &V> {
        self.0
            .iter()
            .map(|(_, v)| match v {
                OneOrMultiple::One(value) => slice::from_ref(value),
                OneOrMultiple::Multiple(values) => values,
            })
            .flat_map(<[V]>::iter)
    }
}

struct MultiMapIter<'a, V>(Option<slice::Iter<'a, V>>);

impl<'a, V> Iterator for MultiMapIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.as_mut().map(slice::Iter::next).flatten()
    }
}

struct MultiMapIterMut<'a, V>(Option<slice::IterMut<'a, V>>);

impl<'a, V> Iterator for MultiMapIterMut<'a, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.as_mut().map(slice::IterMut::next).flatten()
    }
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

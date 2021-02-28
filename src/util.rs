use std::{
    collections::{hash_map::Entry, HashMap},
    hash::Hash,
    iter::Iterator,
    mem::size_of,
    slice::from_ref,
};

pub(crate) fn to_lower_str(string: &str, result: &mut String) {
    for c in string.chars() {
        to_lower_char(c, result);
    }
}

pub(crate) fn to_lower_char(c: char, result: &mut String) {
    for c in c.to_lowercase() {
        result.push(c);
    }
}

pub(crate) fn u32_to_bin_bytes(val: u32) -> [u8; 4] {
    u32::to_le_bytes(val)
    //u32::to_be_bytes(val)
}

pub(crate) fn u32_from_bin(bin: u32) -> u32 {
    u32::from_le(bin)
    //u32::from_be(bin)
}

pub(crate) fn u64_to_bin_bytes(val: u64) -> [u8; size_of::<u64>()] {
    u64::to_le_bytes(val)
    //u32::to_be_bytes(val)
}

pub(crate) fn u64_from_bin(bin: u64) -> u64 {
    u64::from_le(bin)
    //u64::from_be(bin)
}

/// One or multiple value in the multimap associated with a given key.
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
            OneOrMultiple::One(value) => from_ref(value),
            OneOrMultiple::Multiple(values) => &values[..],
        })
    }
}

/// Takes a (reverse) iterator builder `iter` over path parts / components,
/// clears and fills the `string` with the full path, using `/` as separators.
pub(crate) fn build_path_string<'i, F, I>(iter: F, string: &mut String)
where
    F: Fn() -> I,
    I: Iterator<Item = &'i str>,
{
    let (num_parts, len) = iter().fold((0, 0), |(num_parts, len), part| {
        (num_parts + 1, len + part.len())
    });
    debug_assert!(num_parts > 0);

    let len = len + num_parts - 1;

    string.clear();
    string.reserve(len as _);

    let string = unsafe { string.as_mut_vec() };
    unsafe { string.set_len(len as _) };

    // "f  o  o  /  b  a  r  /  b  a  z  .  c  f  g" len = 15
    //  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14

    let mut offset = len;

    for (idx, part) in iter().enumerate() {
        let first = idx == (num_parts - 1);

        debug_assert!(offset >= part.len());
        offset -= part.len();

        unsafe {
            std::ptr::copy_nonoverlapping(
                part.as_ptr(),
                string.as_mut_ptr().offset(offset as _),
                part.len(),
            )
        };

        if !first {
            debug_assert!(offset >= 1);
            offset -= 1;

            *(unsafe { string.get_unchecked_mut(offset) }) = b'/';
        }
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

# minifiletree

A small helper Rust library to gather collections of UTF-8 relative file paths, associate them with unique hashes,
and store them space-efficiently in a binary data blob;
for it to be later serialized/deserialized and used to efficiently look up the string paths by their hashes.

Used data structure is an inverted directory/file tree, with leaf nodes (i.e. files) indexed by the path hashes
and referencing their parent nodes (i.e. folders) recursively.

Path component (and also file name extension) strings are deduplicated, as are the file tree nodes.

Lookup results may be returned as a (reverse) iterator over the path components (including the extension),
or as an owned file path buffer.
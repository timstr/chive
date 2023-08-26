# serialization

_(likely to be renamed at some point)_

A low-level binary format serialization and deserialization library with support for integer and floating point values and arrays of values, UTF-8 strings, and nested sub-archives.

```rust
let archive = Archive::serialize_with(|mut s1| {
    s1.u8(1);
    s1.u16(2);
    s1.array_slice_u8(&[0, 1, 2, 3]);
    s1.array_slice_u64(&[10, 11, 12, 13]);
    s1.string("Testing");

    {
        let mut s2 = s1.subarchive();

        // Can't write to an outer archive while inside a subarchive.
        // The borrow checker kindly enforces this.
        // s1.u8(0);

        s2.u8(3);
        s2.u16(4);
        s2.array_slice_u8(&[20, 21, 22, 23]);
        s2.array_slice_u64(&[30, 31, 32, 33]);
    }
    s1.u8(1);
});

let raw_data = archive.into_vec();
// use raw_data to save to file, send over network, encode as Base64, whatever
```

Individual values are stored as a type tag followed by the binary value. For strings, arrays, and sub-archives, the length is also encoded between the type tag and the value. During deserialization, the type and length can be inspected without reading or consuming the following value to make runtime decisions about how to interpret the archive. Otherwise, during deserialization, strongly-typed values can be read eagerly and easily using the `Result<>`-based interface.

```rust
let archive = Archive::load_from_file("path/to/file.dat")?;
let d = archive.deserialize()?;
let id = d.u16()?;
let values = d.array_slice_u16()?;
let name = d.string()?;
{
    let subarchive = d.subarchive()?;
    let inner_values = subarchive.array_slice_f32()?;
}
```

Arrays can be serialized and deserialized using iterators as well as slices and `Vec`.

```rust
for i in deserializer.array_iter_u16()? {
    println!("{}", i);
}

serializer.array_iter_u16(some_hash_map.keys().cloned());
```

## Features not included

-   Versioning
-   Named fields
-   JSON / BSON / `serde` compatibility

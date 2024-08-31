# chive

A low-level binary format serialization and deserialization library with support for integer and floating point values and arrays of values, UTF-8 strings, and nested sub-archives.

```rust
let chive = Chive::with_chive_in(|mut chive_in| {
    chive_in.u8(1);
    chive_in.u16(2);
    chive_in.array_slice_u8(&[0, 1, 2, 3]);
    chive_in.array_slice_u64(&[10, 11, 12, 13]);
    chive_in.string("Testing");

    {
        let mut nested_chive_in = chive_in.nest();

        // Can't write to an outer chive while inside a nest.
        // The borrow checker kindly enforces this.
        // c1.u8(0);

        nested_chive_in.u8(3);
        nested_chive_in.u16(4);
        nested_chive_in.array_slice_u8(&[20, 21, 22, 23]);
        nested_chive_in.array_slice_u64(&[30, 31, 32, 33]);
    }
    chive_in.u8(1);
});

let raw_data = chive.into_vec();
// use raw_data to save to file, send over network, encode as Base64, whatever
```

Individual values are stored as a type tag followed by the binary value. For strings, arrays, and sub-archives, the length is also encoded between the type tag and the value. During deserialization, the type and length can be inspected without reading or consuming the following value to make runtime decisions about how to interpret the archive. Otherwise, during deserialization, strongly-typed values can be read eagerly and easily using the `Result<>`-based interface.

```rust
let chive = Chive::load_from_file("path/to/file.dat")?;
let chive_out = chive.deserialize()?;
let id = d.u16()?;
let values = chive_out.array_slice_u16()?;
let name = chive_out.string()?;
{
    let nested_chive_out = chive_out.nest()?;
    let inner_values = nested_chive_out.array_slice_f32()?;
}
```

Arrays can be serialized and deserialized using iterators as well as slices and `Vec`.

```rust
for i in chive_out.array_iter_u16()? {
    println!("{}", i);
}

chive_out.array_iter_u16(some_hash_map.keys().cloned());
```

## Features not included

-   Versioning
-   Named fields
-   JSON / BSON / `serde` compatibility
-   Compression

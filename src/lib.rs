#[cfg(test)]
mod test;

use std::{fs, io, marker::PhantomData, path::Path};

/// Trait for a user-defined type that can be serialized and deserialized
/// into a Chive.
pub trait Chivable: Sized {
    /// Serialize self into the ChiveIn by adding all
    /// relevant members in a stable order
    fn chive_in(&self, chive_in: &mut ChiveIn);

    /// Create a new instance of Self by deserializing
    /// all relevant members in the same order they were
    /// serialized by Self::chive_in()
    fn chive_out(chive_out: &mut ChiveOut) -> Result<Self, ()>;
}

/// Default implementation for the unit type
impl Chivable for () {
    fn chive_in(&self, _chive_in: &mut ChiveIn) {
        // Nothing to do
    }

    fn chive_out(_chive_out: &mut ChiveOut) -> Result<Self, ()> {
        Ok(())
    }
}

/// Enum for the set of primitive fixed-size types that are supported
#[derive(PartialEq, Eq, Debug)]
pub enum PrimitiveType {
    Bool,
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    U64,
    I64,
    F32,
    F64,
}

/// Enum for set the of value types that are supported
#[derive(PartialEq, Eq, Debug)]
pub enum ValueType {
    /// A fixed-size primitive, e.g. boolean, integer, or floating point number
    Primitive(PrimitiveType),

    /// A list of values of a common primitive type whose number of elements can be queried
    Array(PrimitiveType),

    /// A utf-8 encoded string
    String,

    /// A chive within. Useful for encapsulating and separating sections of the chive
    /// for different purposes.
    Nest,
}

impl PrimitiveType {
    /// Returns an integer with value 0xF or less, used to uniquely tag each primitive type
    fn to_nibble(&self) -> u8 {
        match self {
            PrimitiveType::Bool => 0x01,
            PrimitiveType::U8 => 0x02,
            PrimitiveType::I8 => 0x03,
            PrimitiveType::U16 => 0x04,
            PrimitiveType::I16 => 0x05,
            PrimitiveType::U32 => 0x06,
            PrimitiveType::I32 => 0x07,
            PrimitiveType::U64 => 0x08,
            PrimitiveType::I64 => 0x09,
            PrimitiveType::F32 => 0x0A,
            PrimitiveType::F64 => 0x0B,
        }
    }

    /// Constructs a PrimitiveType from an integer value as returned by to_nibble()
    fn from_nibble(byte: u8) -> Result<PrimitiveType, ()> {
        match byte {
            0x01 => Ok(PrimitiveType::Bool),
            0x02 => Ok(PrimitiveType::U8),
            0x03 => Ok(PrimitiveType::I8),
            0x04 => Ok(PrimitiveType::U16),
            0x05 => Ok(PrimitiveType::I16),
            0x06 => Ok(PrimitiveType::U32),
            0x07 => Ok(PrimitiveType::I32),
            0x08 => Ok(PrimitiveType::U64),
            0x09 => Ok(PrimitiveType::I64),
            0x0A => Ok(PrimitiveType::F32),
            0x0B => Ok(PrimitiveType::F64),
            _ => Err(()),
        }
    }
}

impl ValueType {
    /// Returns an integer used to uniquely tag each value type
    fn to_byte(&self) -> u8 {
        match self {
            ValueType::Primitive(prim_type) => 0x00 | prim_type.to_nibble(),
            ValueType::Array(prim_type) => 0x10 | prim_type.to_nibble(),
            ValueType::String => 0x20,
            ValueType::Nest => 0x30,
        }
    }

    /// Constructs a ValueType from an integer value as returned by to_byte()
    fn from_byte(byte: u8) -> Result<ValueType, ()> {
        let hi_nibble = byte & 0xF0;
        let lo_nibble = byte & 0x0F;
        match hi_nibble {
            0x00 => Ok(ValueType::Primitive(PrimitiveType::from_nibble(lo_nibble)?)),
            0x10 => Ok(ValueType::Array(PrimitiveType::from_nibble(lo_nibble)?)),
            0x20 => Ok(ValueType::String),
            0x30 => Ok(ValueType::Nest),
            _ => Err(()),
        }
    }
}

/// Helper trait for serializing primitives directly
trait PrimitiveReadWrite {
    /// The number of bytes occupied by the value itself in memory
    const SIZE: usize;

    /// The PrimitiveType that this type corresponds to, e.g. PrimitiveType::I32 for i32
    const TYPE: PrimitiveType;

    /// Write self to the byte vector
    fn write_to(&self, data: &mut Vec<u8>);

    /// Read self from the byte vector.
    /// This method may panic if there are fewer than Self::SIZE bytes in the vector.
    fn read_from(data: &mut ChiveOut) -> Self;
}

/// Macro for implementing the PrimitiveReadWrite helper trait for a given
/// Rust type, given its size in bytes and its corresponding PrimitiveType.
/// The methods `to_be_bytes()` and `from_be_bytes` are used, which exist
/// for all primitive integer and floating point types
macro_rules! impl_primitive_read_write {
    ($primitive: ident, $size: literal, $typetag: expr) => {
        impl PrimitiveReadWrite for $primitive {
            const SIZE: usize = $size;
            const TYPE: PrimitiveType = $typetag;
            fn write_to(&self, data: &mut Vec<u8>) {
                for b in self.to_be_bytes() {
                    data.push(b);
                }
            }
            fn read_from(d: &mut ChiveOut) -> Self {
                let mut bytes = Self::default().to_be_bytes();
                for b in &mut bytes {
                    *b = d.read_byte().unwrap();
                }
                Self::from_be_bytes(bytes)
            }
        }
    };
}

impl_primitive_read_write!(u8, 1, PrimitiveType::U8);
impl_primitive_read_write!(i8, 1, PrimitiveType::I8);
impl_primitive_read_write!(u16, 2, PrimitiveType::U16);
impl_primitive_read_write!(i16, 2, PrimitiveType::I16);
impl_primitive_read_write!(u32, 4, PrimitiveType::U32);
impl_primitive_read_write!(i32, 4, PrimitiveType::I32);
impl_primitive_read_write!(u64, 8, PrimitiveType::U64);
impl_primitive_read_write!(i64, 8, PrimitiveType::I64);
impl_primitive_read_write!(f32, 4, PrimitiveType::F32);
impl_primitive_read_write!(f64, 8, PrimitiveType::F64);

/// Explicit implementation of PrimitiveReadWrite for bool,
/// which does not have from_be_bytes() / to_be_bytes()
impl PrimitiveReadWrite for bool {
    const SIZE: usize = 1;
    const TYPE: PrimitiveType = PrimitiveType::Bool;

    fn write_to(&self, data: &mut Vec<u8>) {
        data.push(if *self { 1 } else { 0 });
    }

    fn read_from(d: &mut ChiveOut) -> bool {
        d.read_byte().unwrap() != 0
    }
}

/// An in-memory archive of serialized data, which is simply a flat sequence
/// of bytes that can be saved, sent, copied, loaded, and deserialized again
/// at a different time and place.
///
/// To serialize data structures, use the [Chive::with_chive_in] method and
/// then use the given [ChiveIn] object to write individual values and objects.
///
/// To deserialize data structures, use the [Chive::chive_out] method and then
/// use the returned [ChiveOut] object to read data in the same order it was
/// written during serialization.
pub struct Chive {
    /// The serialized data. This may have been loaded from an arbitrary file
    /// or created from an arbitrary vector, and so may not have a valid structure.
    /// Validation is performed during deserialization using a Result<> return
    /// type on each deserialization method.
    data: Vec<u8>,
}

/// Public methods
impl Chive {
    /// Create a new Chive instance by serializing data a user-provided function
    /// that receives a [ChiveIn] instance. The body of the function needs to
    /// write all relevant data to the [ChiveIn] object. It is (currently) not
    /// possible to write additional data afterwards.
    ///
    /// Returns a Chive instance containing a flattened representation of all
    /// data that was given to the [ChiveIn] object.
    pub fn with_chive_in<F: Fn(ChiveIn)>(f: F) -> Chive {
        let mut data = Vec::<u8>::new();

        data.push(0);
        data.push(0);
        data.push(0);
        data.push(0);

        let chive_in = ChiveIn::new(&mut data);
        f(chive_in);

        debug_assert!(data.len() >= 4);
        let len_bytes = (data.len() - 4) as u32;
        let [b0, b1, b2, b3] = len_bytes.to_be_bytes();

        data[0] = b0;
        data[1] = b1;
        data[2] = b2;
        data[3] = b3;

        Chive { data }
    }

    /// Get a [ChiveOut] instance to deserialize and retrieve individual values
    /// out of the raw binary data.
    pub fn chive_out<'a>(&'a self) -> Result<ChiveOut<'a>, ()> {
        if self.data.len() < 4 {
            return Err(());
        }
        let len =
            u32::from_be_bytes([self.data[0], self.data[1], self.data[2], self.data[3]]) as usize;
        let slice = &self.data[4..];
        if len != slice.len() {
            return Err(());
        }
        Ok(ChiveOut {
            data: slice,
            position: 0,
        })
    }

    /// Write the binary contents the chive to a file at the given path
    pub fn dump_to_file(&self, path: &Path) -> Result<(), io::Error> {
        // TODO: magic number?
        fs::write(path, &self.data)?;
        Ok(())
    }

    /// Read the file at the given path and load its binary data into
    /// a new Chive instance. No validation of the contents is performed.
    pub fn load_from_file(path: &Path) -> Result<Chive, io::Error> {
        // TODO: magic number?
        let data = fs::read(path)?;
        Ok(Chive { data })
    }

    /// Take the underlying vector of bytes
    pub fn into_vec(self) -> Vec<u8> {
        self.data
    }

    /// Construct a new Chive instance from a vector of bytes.
    /// No validation of the contents is performed.
    pub fn from_vec(data: Vec<u8>) -> Chive {
        Chive { data }
    }
}

/// ChiveIn is used to serialize user-provided data in to a [Chive] instance.
pub struct ChiveIn<'a> {
    /// Mutable reference to a vector of bytes which all serialized data
    /// will be written to
    data: &'a mut Vec<u8>,
}

/// Private methods
impl<'a> ChiveIn<'a> {
    /// Create a new ChiveIn instance that will deserialize the given bytes
    fn new(data: &'a mut Vec<u8>) -> ChiveIn<'a> {
        ChiveIn { data }
    }

    /// Helper method to write a primitive
    fn write_primitive<T: PrimitiveReadWrite>(&mut self, x: T) {
        self.data.reserve(u8::SIZE + T::SIZE);
        self.data.push(ValueType::Primitive(T::TYPE).to_byte());
        x.write_to(self.data);
    }

    /// Helper method to write a slice of primitives
    fn write_primitive_array_slice<T: PrimitiveReadWrite>(&mut self, x: &[T]) {
        self.data
            .reserve(u8::SIZE + u32::SIZE + (x.len() * T::SIZE));
        self.data.push(ValueType::Array(T::TYPE).to_byte());
        let len = x.len() as u32;
        len.write_to(self.data);
        for xi in x {
            xi.write_to(self.data);
        }
    }

    /// Helper method to write an iterator of primitives
    fn write_primitive_array_iter<I: Iterator>(&mut self, mut it: I)
    where
        I::Item: PrimitiveReadWrite,
    {
        self.data.push(ValueType::Array(I::Item::TYPE).to_byte());
        let array_start_index = self.data.len();
        let mut n_items: u32 = 0;
        n_items.write_to(self.data);
        while let Some(x) = it.next() {
            x.write_to(self.data);
            n_items += 1;
        }
        for (i, b) in n_items.to_be_bytes().iter().enumerate() {
            self.data[array_start_index + i] = *b;
        }
    }
}

/// Public methods
impl<'a> ChiveIn<'a> {
    /// Write a single u8 value
    pub fn u8(&mut self, x: u8) {
        self.write_primitive::<u8>(x);
    }

    /// Write a single i8 value
    pub fn i8(&mut self, x: i8) {
        self.write_primitive::<i8>(x);
    }

    /// Write a single u16 value
    pub fn u16(&mut self, x: u16) {
        self.write_primitive::<u16>(x);
    }

    /// Write a single i16 value
    pub fn i16(&mut self, x: i16) {
        self.write_primitive::<i16>(x);
    }

    /// Write a single u32 value
    pub fn u32(&mut self, x: u32) {
        self.write_primitive::<u32>(x);
    }

    /// Write a single i32 value
    pub fn i32(&mut self, x: i32) {
        self.write_primitive::<i32>(x);
    }

    /// Write a single u64 value
    pub fn u64(&mut self, x: u64) {
        self.write_primitive::<u64>(x);
    }

    /// Write a single i64 value
    pub fn i64(&mut self, x: i64) {
        self.write_primitive::<i64>(x);
    }

    /// Write a single f32 value
    pub fn f32(&mut self, x: f32) {
        self.write_primitive::<f32>(x);
    }

    /// Write a single f64 value
    pub fn f64(&mut self, x: f64) {
        self.write_primitive::<f64>(x);
    }

    /// Write an array of u8 values from a slice
    pub fn array_slice_u8(&mut self, x: &[u8]) {
        self.write_primitive_array_slice::<u8>(x);
    }

    /// Write an array of i8 values from a slice
    pub fn array_slice_i8(&mut self, x: &[i8]) {
        self.write_primitive_array_slice::<i8>(x);
    }

    /// Write an array of u16 values from a slice
    pub fn array_slice_u16(&mut self, x: &[u16]) {
        self.write_primitive_array_slice::<u16>(x);
    }

    /// Write an array of i16 values from a slice
    pub fn array_slice_i16(&mut self, x: &[i16]) {
        self.write_primitive_array_slice::<i16>(x);
    }

    /// Write an array of u32 values from a slice
    pub fn array_slice_u32(&mut self, x: &[u32]) {
        self.write_primitive_array_slice::<u32>(x);
    }

    /// Write an array of i32 values from a slice
    pub fn array_slice_i32(&mut self, x: &[i32]) {
        self.write_primitive_array_slice::<i32>(x);
    }

    /// Write an array of u64 values from a slice
    pub fn array_slice_u64(&mut self, x: &[u64]) {
        self.write_primitive_array_slice::<u64>(x);
    }

    /// Write an array of i64 values from a slice
    pub fn array_slice_i64(&mut self, x: &[i64]) {
        self.write_primitive_array_slice::<i64>(x);
    }

    /// Write an array of f32 values from a slice
    pub fn array_slice_f32(&mut self, x: &[f32]) {
        self.write_primitive_array_slice::<f32>(x);
    }

    /// Write an array of f64 values from a slice
    pub fn array_slice_f64(&mut self, x: &[f64]) {
        self.write_primitive_array_slice::<f64>(x);
    }

    /// Write an array of u8 values from an iterator
    pub fn array_iter_u8<I: Iterator<Item = u8>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write an array of i8 values from an iterator
    pub fn array_iter_i8<I: Iterator<Item = i8>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write an array of u16 values from an iterator
    pub fn array_iter_u16<I: Iterator<Item = u16>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write an array of i16 values from an iterator
    pub fn array_iter_i16<I: Iterator<Item = i16>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write an array of u32 values from an iterator
    pub fn array_iter_u32<I: Iterator<Item = u32>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write an array of i32 values from an iterator
    pub fn array_iter_i32<I: Iterator<Item = i32>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write an array of u64 values from an iterator
    pub fn array_iter_u64<I: Iterator<Item = u64>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write an array of i64 values from an iterator
    pub fn array_iter_i64<I: Iterator<Item = i64>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write an array of f32 values from an iterator
    pub fn array_iter_f32<I: Iterator<Item = f32>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write an array of f64 values from an iterator
    pub fn array_iter_f64<I: Iterator<Item = f64>>(&mut self, it: I) {
        self.write_primitive_array_iter(it);
    }

    /// Write a string
    pub fn string(&mut self, x: &str) {
        let bytes = x.as_bytes();
        self.data.reserve(u8::SIZE + u32::SIZE + bytes.len());
        self.data.push(ValueType::String.to_byte());
        let len = bytes.len() as u32;
        len.write_to(self.data);
        for b in bytes {
            self.data.push(*b);
        }
    }

    /// Write a nested sub-chive. This creates a contiguous section of bytes
    /// which is cleanly separated from all data before and after the nested
    /// sub-chive. This is useful for separating concerns and (de)serializing
    /// separate complex data structures without fear that deserializing one
    ///  may read off the end and into the start of the next.
    pub fn nest<F: FnOnce(ChiveIn)>(&mut self, f: F) {
        self.data.push(ValueType::Nest.to_byte());

        let prefix_index = self.data.len();

        self.data.push(0);
        self.data.push(0);
        self.data.push(0);
        self.data.push(0);

        let len_before = self.data.len();

        f(ChiveIn::new(self.data));

        let len_after = self.data.len();
        debug_assert!(len_after >= len_before);
        let len = (len_after - len_before) as u32;
        let [b0, b1, b2, b3] = len.to_be_bytes();

        self.data[prefix_index + 0] = b0;
        self.data[prefix_index + 1] = b1;
        self.data[prefix_index + 2] = b2;
        self.data[prefix_index + 3] = b3;
    }

    /// Write a user-provided object which implements Chivable
    pub fn chivable<T: Chivable>(&mut self, chivable: &T) {
        chivable.chive_in(self);
    }
}

/// Iterator for reading values out of a serialized array in a [Chive] instance
/// one value at a time.
pub struct ChiveOutIterator<'a, T> {
    /// A ChiveOut instance pointing to a slice of serialized data containing an array
    chive_out: ChiveOut<'a>,

    /// PhantomData used to bake the type parameter T into the iterator
    _phantom_data: PhantomData<T>,
}

impl<'a, T> ChiveOutIterator<'a, T> {
    /// Construct a new ChiveOutIterator. The chive_out instance is expected
    /// to point to an homogenous array of serialized primitive values.
    fn new(chive_out: ChiveOut<'a>) -> ChiveOutIterator<'a, T>
    where
        T: PrimitiveReadWrite,
    {
        debug_assert_eq!(chive_out.remaining_len() % T::SIZE, 0);
        ChiveOutIterator {
            chive_out,
            _phantom_data: PhantomData,
        }
    }
}

/// Iterator implementation for ChiveOutIterator
impl<'a, T: PrimitiveReadWrite> Iterator for ChiveOutIterator<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.chive_out.is_empty() {
            return None;
        }
        debug_assert!(self.chive_out.remaining_len() >= T::SIZE);
        Some(T::read_from(&mut self.chive_out))
    }
}

/// ExactSizeIterator implementation for ChiveOutIterator
impl<'a, T: PrimitiveReadWrite> ExactSizeIterator for ChiveOutIterator<'a, T> {
    fn len(&self) -> usize {
        debug_assert_eq!(self.chive_out.remaining_len() % T::SIZE, 0);
        self.chive_out.remaining_len() / T::SIZE
    }
}

/// ChiveOut is used to deserialize data out of an existing [Chive] instance.
pub struct ChiveOut<'a> {
    data: &'a [u8],
    position: usize,
}

/// Private methods
impl<'a> ChiveOut<'a> {
    /// Create a new ChiveOut instance for deserializing the given slice of bytes
    fn new(data: &'a [u8]) -> ChiveOut<'a> {
        ChiveOut { data, position: 0 }
    }

    /// Get the number of bytes that have yet to be read
    fn remaining_len(&self) -> usize {
        let l = self.data.len();
        debug_assert!(self.position <= l);
        return l - self.position;
    }

    /// Read the next byte and advance past it
    fn read_byte(&mut self) -> Result<u8, ()> {
        if self.position >= self.data.len() {
            Err(())
        } else {
            let b = self.data[self.position];
            self.position += 1;
            Ok(b)
        }
    }

    /// Read the next byte without advancing past it
    fn peek_byte(&self, offset: usize) -> Result<u8, ()> {
        if (self.position + offset) >= self.data.len() {
            Err(())
        } else {
            Ok(self.data[self.position + offset])
        }
    }

    /// Try to perform an operation, get its result, and
    /// rollback the position in the underlying byte vector
    /// if it failed.
    fn reset_on_error<T: 'a, F: FnOnce(&mut ChiveOut<'a>) -> Result<T, ()>>(
        &mut self,
        f: F,
    ) -> Result<T, ()> {
        let original_position = self.position;
        let result = f(self);
        if result.is_err() {
            self.position = original_position;
        }
        result
    }

    /// Read a single primitive, checking for its type tag first and then
    /// reading its value
    fn read_primitive<T: PrimitiveReadWrite + 'static>(&mut self) -> Result<T, ()> {
        self.reset_on_error(|d| {
            if d.remaining_len() < (u8::SIZE + T::SIZE) {
                return Err(());
            }
            let the_type = ValueType::from_byte(d.read_byte()?)?;
            if the_type != ValueType::Primitive(T::TYPE) {
                return Err(());
            }
            Ok(T::read_from(d))
        })
    }

    /// Read an array of primitives to a vector, checking for its tag type and length
    /// first and then reading its values
    fn read_primitive_array_slice<T: PrimitiveReadWrite + 'static>(
        &mut self,
    ) -> Result<Vec<T>, ()> {
        self.reset_on_error(|d| {
            if d.remaining_len() < (u8::SIZE + u32::SIZE) {
                return Err(());
            }
            let the_type = ValueType::from_byte(d.read_byte()?)?;
            if the_type != ValueType::Array(T::TYPE) {
                return Err(());
            }
            let len = u32::read_from(d) as usize;
            if d.remaining_len() < (len * T::SIZE) {
                return Err(());
            }
            Ok((0..len).map(|_| T::read_from(d)).collect())
        })
    }

    /// Create an iterator that visits all primitives in an array, first checking
    /// the tag type and length.
    fn read_primitive_array_iter<'b, T: PrimitiveReadWrite + 'static>(
        &'b mut self,
    ) -> Result<ChiveOutIterator<'b, T>, ()> {
        self.reset_on_error(|d| {
            if d.remaining_len() < (u8::SIZE + u32::SIZE) {
                return Err(());
            }
            let the_type = ValueType::from_byte(d.read_byte()?)?;
            if the_type != ValueType::Array(T::TYPE) {
                return Err(());
            }
            let len = u32::read_from(d) as usize;
            let byte_len = len * T::SIZE;
            if d.remaining_len() < byte_len {
                return Err(());
            }
            let d2 = ChiveOut::new(&d.data[d.position..d.position + byte_len]);
            d.position += byte_len;
            Ok(ChiveOutIterator::new(d2))
        })
    }
}

/// Public methods
impl<'a> ChiveOut<'a> {
    /// Read a single u8 value
    pub fn u8(&mut self) -> Result<u8, ()> {
        self.read_primitive::<u8>()
    }

    /// Read a single i8 value
    pub fn i8(&mut self) -> Result<i8, ()> {
        self.read_primitive::<i8>()
    }

    /// Read a single u16 value
    pub fn u16(&mut self) -> Result<u16, ()> {
        self.read_primitive::<u16>()
    }

    /// Read a single i16 value
    pub fn i16(&mut self) -> Result<i16, ()> {
        self.read_primitive::<i16>()
    }

    /// Read a single u32 value
    pub fn u32(&mut self) -> Result<u32, ()> {
        self.read_primitive::<u32>()
    }

    /// Read a single i32 value
    pub fn i32(&mut self) -> Result<i32, ()> {
        self.read_primitive::<i32>()
    }

    /// Read a single u64 value
    pub fn u64(&mut self) -> Result<u64, ()> {
        self.read_primitive::<u64>()
    }

    /// Read a single i64 value
    pub fn i64(&mut self) -> Result<i64, ()> {
        self.read_primitive::<i64>()
    }

    /// Read a single f32 value
    pub fn f32(&mut self) -> Result<f32, ()> {
        self.read_primitive::<f32>()
    }

    /// Read a single f64 value
    pub fn f64(&mut self) -> Result<f64, ()> {
        self.read_primitive::<f64>()
    }

    /// Read an array of u8 values into a Vec
    pub fn array_slice_u8(&mut self) -> Result<Vec<u8>, ()> {
        self.read_primitive_array_slice::<u8>()
    }

    /// Read an array of i8 values into a Vec
    pub fn array_slice_i8(&mut self) -> Result<Vec<i8>, ()> {
        self.read_primitive_array_slice::<i8>()
    }

    /// Read an array of u16 values into a Vec
    pub fn array_slice_u16(&mut self) -> Result<Vec<u16>, ()> {
        self.read_primitive_array_slice::<u16>()
    }

    /// Read an array of i16 values into a Vec
    pub fn array_slice_i16(&mut self) -> Result<Vec<i16>, ()> {
        self.read_primitive_array_slice::<i16>()
    }

    /// Read an array of u32 values into a Vec
    pub fn array_slice_u32(&mut self) -> Result<Vec<u32>, ()> {
        self.read_primitive_array_slice::<u32>()
    }

    /// Read an array of i32 values into a Vec
    pub fn array_slice_i32(&mut self) -> Result<Vec<i32>, ()> {
        self.read_primitive_array_slice::<i32>()
    }

    /// Read an array of u64 values into a Vec
    pub fn array_slice_u64(&mut self) -> Result<Vec<u64>, ()> {
        self.read_primitive_array_slice::<u64>()
    }

    /// Read an array of i64 values into a Vec
    pub fn array_slice_i64(&mut self) -> Result<Vec<i64>, ()> {
        self.read_primitive_array_slice::<i64>()
    }

    /// Read an array of f32 values into a Vec
    pub fn array_slice_f32(&mut self) -> Result<Vec<f32>, ()> {
        self.read_primitive_array_slice::<f32>()
    }

    /// Read an array of f64 values into a Vec
    pub fn array_slice_f64(&mut self) -> Result<Vec<f64>, ()> {
        self.read_primitive_array_slice::<f64>()
    }

    /// Read an array of u8 values into an iterator
    pub fn array_iter_u8<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, u8>, ()> {
        self.read_primitive_array_iter::<u8>()
    }

    /// Read an array of i8 values into an iterator
    pub fn array_iter_i8<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, i8>, ()> {
        self.read_primitive_array_iter::<i8>()
    }

    /// Read an array of u16 values into an iterator
    pub fn array_iter_u16<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, u16>, ()> {
        self.read_primitive_array_iter::<u16>()
    }

    /// Read an array of i16 values into an iterator
    pub fn array_iter_i16<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, i16>, ()> {
        self.read_primitive_array_iter::<i16>()
    }

    /// Read an array of u32 values into an iterator
    pub fn array_iter_u32<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, u32>, ()> {
        self.read_primitive_array_iter::<u32>()
    }

    /// Read an array of i32 values into an iterator
    pub fn array_iter_i32<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, i32>, ()> {
        self.read_primitive_array_iter::<i32>()
    }

    /// Read an array of u64 values into an iterator
    pub fn array_iter_u64<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, u64>, ()> {
        self.read_primitive_array_iter::<u64>()
    }

    /// Read an array of i64 values into an iterator
    pub fn array_iter_i64<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, i64>, ()> {
        self.read_primitive_array_iter::<i64>()
    }

    /// Read an array of f32 values into an iterator
    pub fn array_iter_f32<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, f32>, ()> {
        self.read_primitive_array_iter::<f32>()
    }

    /// Read an array of f64 values into an iterator
    pub fn array_iter_f64<'b>(&'b mut self) -> Result<ChiveOutIterator<'b, f64>, ()> {
        self.read_primitive_array_iter::<f64>()
    }

    /// Read a string
    pub fn string(&mut self) -> Result<String, ()> {
        if self.remaining_len() < (u8::SIZE + u32::SIZE) {
            return Err(());
        }
        let the_type = ValueType::from_byte(self.read_byte()?)?;
        if the_type != ValueType::String {
            return Err(());
        }
        let len = u32::read_from(self) as usize;
        if self.remaining_len() < len {
            return Err(());
        }
        let slice = &self.data[self.position..(self.position + len)];
        self.position += len;
        let str_slice = std::str::from_utf8(slice).map_err(|_| ())?;
        Ok(str_slice.to_string())
    }

    /// Read a nested sub-chive
    pub fn nest<'b>(&'b mut self) -> Result<ChiveOut<'b>, ()> {
        if self.remaining_len() < (u8::SIZE + u32::SIZE) {
            return Err(());
        }
        let the_type = ValueType::from_byte(self.read_byte()?)?;
        if the_type != ValueType::Nest {
            return Err(());
        }
        let len = u32::read_from(self) as usize;
        if self.remaining_len() < len {
            return Err(());
        }
        let nest_slice: &[u8] = &self.data[self.position..(self.position + len)];
        self.position += len;
        Ok(ChiveOut::new(nest_slice))
    }

    /// Read a user-provided object which implements Chivable.
    /// The type of the object is not checked, only the types
    /// of individual values.
    pub fn chivable<T: Chivable>(&mut self) -> Result<T, ()> {
        T::chive_out(self)
    }

    /// Read the type of the next value
    pub fn peek_type(&self) -> Result<ValueType, ()> {
        ValueType::from_byte(self.peek_byte(0)?)
    }

    /// If the next type is an array, string, or nested chive,
    /// get its length, in bytes
    pub fn peek_length_bytes(&self) -> Result<usize, ()> {
        let the_type = ValueType::from_byte(self.peek_byte(0)?)?;
        if let ValueType::Primitive(_) = the_type {
            return Err(());
        }
        Ok(u32::from_be_bytes([
            self.peek_byte(1)?,
            self.peek_byte(2)?,
            self.peek_byte(3)?,
            self.peek_byte(4)?,
        ]) as usize)
    }

    /// Returns true iff the chive contains no more data to read
    pub fn is_empty(&self) -> bool {
        return self.position == self.data.len();
    }
}

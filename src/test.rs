use crate::{Chive, PrimitiveType, ValueType};

#[test]
fn end_to_end_test() {
    let chive = Chive::with_chive_in(|mut ci| {
        ci.u8(1);
        ci.u16(2);
        ci.array_slice_u8(&[0, 1, 2, 3]);
        ci.array_slice_u64(&[10, 11, 12, 13]);
        ci.string("Testing");

        ci.nest(|mut ci| {
            ci.u8(3);
            ci.u16(4);
            ci.array_slice_u8(&[20, 21, 22, 23]);
            ci.array_slice_u64(&[30, 31, 32, 33]);
        });

        ci.u8(1);
    });

    let mut co1 = chive.chive_out().unwrap();
    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Primitive(PrimitiveType::U8)
    );
    assert!(co1.peek_length_bytes().is_err());
    assert_eq!(co1.u8().unwrap(), 1);
    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Primitive(PrimitiveType::U16)
    );
    assert!(co1.peek_length_bytes().is_err());
    assert_eq!(co1.u16().unwrap(), 2);
    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Array(PrimitiveType::U8)
    );
    assert_eq!(co1.peek_length_bytes().unwrap(), 4);
    assert_eq!(co1.array_slice_u8().unwrap(), vec![0, 1, 2, 3]);
    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Array(PrimitiveType::U64)
    );
    assert_eq!(co1.peek_length_bytes().unwrap(), 4);
    assert_eq!(co1.array_slice_u64().unwrap(), vec![10, 11, 12, 13]);
    assert_eq!(co1.peek_type().unwrap(), ValueType::String);
    assert_eq!(co1.peek_length_bytes().unwrap(), "Testing".as_bytes().len());
    assert_eq!(co1.string().unwrap(), "Testing");

    assert_eq!(co1.peek_type().unwrap(), ValueType::Nest);
    {
        let mut co2 = co1.nest().unwrap();
        assert_eq!(
            co2.peek_type().unwrap(),
            ValueType::Primitive(PrimitiveType::U8)
        );
        assert!(co2.peek_length_bytes().is_err());
        assert_eq!(co2.u8().unwrap(), 3);
        assert_eq!(
            co2.peek_type().unwrap(),
            ValueType::Primitive(PrimitiveType::U16)
        );
        assert!(co2.peek_length_bytes().is_err());
        assert_eq!(co2.u16().unwrap(), 4);
        assert_eq!(
            co2.peek_type().unwrap(),
            ValueType::Array(PrimitiveType::U8)
        );
        assert_eq!(co2.peek_length_bytes().unwrap(), 4);
        assert_eq!(co2.array_slice_u8().unwrap(), vec![20, 21, 22, 23]);
        assert_eq!(
            co2.peek_type().unwrap(),
            ValueType::Array(PrimitiveType::U64)
        );
        assert_eq!(co2.peek_length_bytes().unwrap(), 4);
        assert_eq!(co2.array_slice_u64().unwrap(), vec![30, 31, 32, 33]);
        assert!(co2.peek_type().is_err());
        assert!(co2.peek_length_bytes().is_err());
        assert!(co2.is_empty());
    }

    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Primitive(PrimitiveType::U8)
    );
    assert!(co1.peek_length_bytes().is_err());
    assert_eq!(co1.u8().unwrap(), 1);

    assert!(co1.peek_type().is_err());
    assert!(co1.peek_length_bytes().is_err());
    assert!(co1.is_empty());
}

#[test]
fn empty_nest_test() {
    let chive = Chive::with_chive_in(|mut ci| {
        ci.u8(0xAA);
        ci.nest(|_| {});
        ci.u8(0xBB);
    });

    let mut co1 = chive.chive_out().unwrap();
    assert_eq!(co1.u8().unwrap(), 0xAA);
    {
        let co2 = co1.nest().unwrap();
        assert!(co2.is_empty());
    }
    assert_eq!(co1.u8().unwrap(), 0xBB);
}

#[test]
fn nested_empty_nest_test() {
    let chive = Chive::with_chive_in(|mut ci| {
        ci.u8(0xAA);
        ci.nest(|mut ci| {
            ci.u8(0x11);
            {
                ci.nest(|_| {});
            }
            ci.u8(0x22);
        });
        ci.u8(0xBB);
    });

    let mut co1 = chive.chive_out().unwrap();
    assert_eq!(co1.u8().unwrap(), 0xAA);
    {
        let mut co2 = co1.nest().unwrap();
        assert_eq!(co2.u8().unwrap(), 0x11);
        {
            let co3 = co2.nest().unwrap();
            assert!(co3.is_empty());
        }
        assert_eq!(co2.u8().unwrap(), 0x22);
        assert!(co2.is_empty());
    }
    assert_eq!(co1.u8().unwrap(), 0xBB);
    assert!(co1.is_empty());
}

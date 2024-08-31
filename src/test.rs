use crate::{Chive, PrimitiveType, ValueType};

#[test]
fn end_to_end_test() {
    let chive = Chive::with_chive_in(|mut ci1| {
        ci1.u8(1);
        ci1.u16(2);
        ci1.array_slice_u8(&[0, 1, 2, 3]);
        ci1.array_slice_u64(&[10, 11, 12, 13]);
        ci1.string("Testing");

        {
            let mut ci2 = ci1.nest();

            // YASSSS this should fail
            // s1.u8(0);

            ci2.u8(3);
            ci2.u16(4);
            ci2.array_slice_u8(&[20, 21, 22, 23]);
            ci2.array_slice_u64(&[30, 31, 32, 33]);
        }
        ci1.u8(1);
    });

    let mut co1 = chive.chive_out().unwrap();
    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Primitive(PrimitiveType::U8)
    );
    assert!(co1.peek_length().is_err());
    assert_eq!(co1.u8().unwrap(), 1);
    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Primitive(PrimitiveType::U16)
    );
    assert!(co1.peek_length().is_err());
    assert_eq!(co1.u16().unwrap(), 2);
    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Array(PrimitiveType::U8)
    );
    assert_eq!(co1.peek_length().unwrap(), 4);
    assert_eq!(co1.array_slice_u8().unwrap(), vec![0, 1, 2, 3]);
    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Array(PrimitiveType::U64)
    );
    assert_eq!(co1.peek_length().unwrap(), 4);
    assert_eq!(co1.array_slice_u64().unwrap(), vec![10, 11, 12, 13]);
    assert_eq!(co1.peek_type().unwrap(), ValueType::String);
    assert_eq!(co1.peek_length().unwrap(), "Testing".as_bytes().len());
    assert_eq!(co1.string().unwrap(), "Testing");

    assert_eq!(co1.peek_type().unwrap(), ValueType::Nest);
    {
        let mut d2 = co1.nest().unwrap();
        assert_eq!(
            d2.peek_type().unwrap(),
            ValueType::Primitive(PrimitiveType::U8)
        );
        assert!(d2.peek_length().is_err());
        assert_eq!(d2.u8().unwrap(), 3);
        assert_eq!(
            d2.peek_type().unwrap(),
            ValueType::Primitive(PrimitiveType::U16)
        );
        assert!(d2.peek_length().is_err());
        assert_eq!(d2.u16().unwrap(), 4);
        assert_eq!(d2.peek_type().unwrap(), ValueType::Array(PrimitiveType::U8));
        assert_eq!(d2.peek_length().unwrap(), 4);
        assert_eq!(d2.array_slice_u8().unwrap(), vec![20, 21, 22, 23]);
        assert_eq!(
            d2.peek_type().unwrap(),
            ValueType::Array(PrimitiveType::U64)
        );
        assert_eq!(d2.peek_length().unwrap(), 4);
        assert_eq!(d2.array_slice_u64().unwrap(), vec![30, 31, 32, 33]);
        assert!(d2.peek_type().is_err());
        assert!(d2.peek_length().is_err());
        assert!(d2.is_empty());
    }

    assert_eq!(
        co1.peek_type().unwrap(),
        ValueType::Primitive(PrimitiveType::U8)
    );
    assert!(co1.peek_length().is_err());
    assert_eq!(co1.u8().unwrap(), 1);

    assert!(co1.peek_type().is_err());
    assert!(co1.peek_length().is_err());
    assert!(co1.is_empty());
}

#[test]
fn empty_nest_test() {
    let chive = Chive::with_chive_in(|mut ci| {
        ci.u8(0xAA);
        {
            ci.nest();
        }
        ci.u8(0xBB);
    });

    let mut d1 = chive.chive_out().unwrap();
    assert_eq!(d1.u8().unwrap(), 0xAA);
    {
        let d2 = d1.nest().unwrap();
        assert!(d2.is_empty());
    }
    assert_eq!(d1.u8().unwrap(), 0xBB);
}

#[test]
fn nested_empty_nest_test() {
    let chive = Chive::with_chive_in(|mut ci1| {
        ci1.u8(0xAA);
        {
            let mut ci2 = ci1.nest();
            ci2.u8(0x11);
            {
                ci2.nest();
            }
            ci2.u8(0x22);
        }
        ci1.u8(0xBB);
    });

    let mut co1 = chive.chive_out().unwrap();
    assert_eq!(co1.u8().unwrap(), 0xAA);
    {
        let mut co2 = co1.nest().unwrap();
        assert_eq!(co2.u8().unwrap(), 0x11);
        {
            let d3 = co2.nest().unwrap();
            assert!(d3.is_empty());
        }
        assert_eq!(co2.u8().unwrap(), 0x22);
        assert!(co2.is_empty());
    }
    assert_eq!(co1.u8().unwrap(), 0xBB);
    assert!(co1.is_empty());
}

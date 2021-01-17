use sled;

use serde::{Deserialize, Serialize};
use zerocopy::{AsBytes, FromBytes, LayoutVerified, Unaligned};

use std::convert::TryInto;

/// This trait converts between types and a bunch of bytes.
///   * `In` is the type you pass to the functions to specify a key or create an IVec.
///   * `Encoded` is an intermediate step which derefs to a byte slice. This is usually a `Vec<u8>` or `[u8; n]`. If `In` can deref to a byte slice without conversion, this is equal to `In`.
///   * `Out` is the type you get when decoding an `IVec`. Often equivalent to `In`, but sometimes it's useful to have `In = &'a T` and `Out = T`.
///
/// Open questions:
///   * Do we split this into Encode/Decode traits? For keys it is often sufficient to Encode.
///   * Encode is currently assumed to be infallible. Do we need an error path here?
///   * Decode may fail. Do we wish to return a `Result` instead of an `Option` for better error messages? Do we use a catch-all `sled::Error::DecodeError` for a simpler public API?
///   * Do we find a better name that doesn't clash with serde's Serialize/Deserialize?
pub trait Encoder<'a> {
    type In;
    type Encoded: AsRef<[u8]>;
    type Out;

    fn encode(d: Self::In) -> Self::Encoded;
    fn decode(bytes: &'a [u8]) -> Option<Self::Out>;
}

/// This wraps an IVec and an Encoder.
pub struct IVecWrapper<E>
where
    for<'a> E: Encoder<'a>,
{
    ivec: sled::IVec,
    _e: std::marker::PhantomData<E>,
}

impl<E> IVecWrapper<E>
where
    for<'a> E: Encoder<'a>,
{
    pub fn new(ivec: sled::IVec) -> Self {
        Self {
            ivec,
            _e: std::marker::PhantomData,
        }
    }
    pub fn from<'a>(value: <E as Encoder<'a>>::In) -> Self {
        Self::new(sled::IVec::from(E::encode(value).as_ref()))
    }
    pub fn decode<'a>(&'a self) -> Option<<E as Encoder<'a>>::Out> {
        E::decode(&self.ivec)
    }
}

/// This wraps a Tree with two Encoders (for keys and values repectively) such that insert() and get() are strongly typed.
pub struct TreeWrapper<K, V>
where
    for<'a> K: Encoder<'a>,
    for<'a> V: Encoder<'a>,
{
    tree: sled::Tree,
    _k: std::marker::PhantomData<K>,
    _v: std::marker::PhantomData<V>,
}

impl<K, V> TreeWrapper<K, V>
where
    for<'a> K: Encoder<'a>,
    for<'a> V: Encoder<'a>,
{
    pub fn new(tree: sled::Tree) -> Self {
        Self {
            tree,
            _k: std::marker::PhantomData,
            _v: std::marker::PhantomData,
        }
    }

    pub fn insert<'a, 'b>(
        &self,
        key: <K as Encoder<'a>>::In,
        value: <V as Encoder<'b>>::In,
    ) -> sled::Result<Option<IVecWrapper<V>>> {
        self.tree
            .insert(K::encode(key), IVecWrapper::<V>::from(value).ivec)
            .map(|res| res.map(|ivec| IVecWrapper::new(ivec)))
    }

    pub fn get<'a>(&self, key: <K as Encoder<'a>>::In) -> sled::Result<Option<IVecWrapper<V>>> {
        self.tree
            .get(K::encode(key))
            .map(|res| res.map(|ivec| IVecWrapper::new(ivec)))
    }
}

// Now let's test this in practice using a few common encodings

/// Encode and Decode [u8] slices
struct DefaultEncoder();
impl<'a> Encoder<'a> for DefaultEncoder {
    type In = &'a [u8];
    type Encoded = &'a [u8];
    type Out = &'a [u8];

    fn encode(d: Self::In) -> Self::Encoded {
        d
    }

    fn decode(bytes: &'a [u8]) -> Option<Self::Out> {
        Some(bytes)
    }
}

#[test]
fn test_default_encoder() -> sled::Result<()> {
    let db = sled::Config::default().temporary(true).open()?;

    let tree = TreeWrapper::<DefaultEncoder, DefaultEncoder>::new(db.open_tree("u8_u8")?);
    tree.insert(b"key", b"value")?;

    // Unfortunately, the old AsRef-magic no longer works - Encoder::In is not guaranteed to be a reference (see u128 example below).
    // Hence, Passing a &str instead of &[u8] is a compile time error.
    // Maybe in the future specialization allows us to use AsRef or Into as needed, depending on the type? I havent't checked.

    // We're borrowing from the ivec, so we need to keep the ivec alive by assigning it to a variable.
    let ivec = tree.get(b"key")?.expect("Value not found");
    let value = ivec.decode().expect("Decoding failed");
    assert_eq!(value, b"value");
    Ok(())
}

/// Encode and Decode utf8 str slices
struct StringEncoder();
impl<'a> Encoder<'a> for StringEncoder {
    type In = &'a str;
    type Encoded = &'a str;
    type Out = &'a str;

    fn encode(d: Self::In) -> Self::Encoded {
        d
    }

    fn decode(bytes: &'a [u8]) -> Option<Self::Out> {
        std::str::from_utf8(bytes).ok()
    }
}

#[test]
fn test_str_encoder() -> sled::Result<()> {
    let db = sled::Config::default().temporary(true).open()?;

    let tree = TreeWrapper::<StringEncoder, StringEncoder>::new(db.open_tree("str_str")?);
    tree.insert("key", "value")?;
    // This will not compile:
    // tree.insert(b"key", b"value")?;
    let res = tree.get("key")?.expect("Value not found");
    let value = res.decode().expect("Decoding failed");
    assert_eq!(value, "value");
    Ok(())
}

/// Encode and Decode integers as big endian, for properly ordered keys.
/// As `.to_be_bytes()` isn't part of any trait, we cannot easily generalize this over all ints, so let's pick one at random.
struct BigEndianU128Encoder();
impl<'a> Encoder<'a> for BigEndianU128Encoder {
    type In = u128;
    type Encoded = [u8; 16];
    type Out = u128;

    fn encode(d: Self::In) -> Self::Encoded {
        d.to_be_bytes()
    }

    fn decode(bytes: &'a [u8]) -> Option<Self::Out> {
        let array = bytes.try_into().ok()?;
        Some(u128::from_be_bytes(array))
    }
}

#[test]
fn test_u128_encoder() -> sled::Result<()> {
    let db = sled::Config::default().temporary(true).open()?;

    let tree =
        TreeWrapper::<BigEndianU128Encoder, BigEndianU128Encoder>::new(db.open_tree("int_int")?);
    tree.insert(12345, 42)?;
    // No need to keep the ivec alive here.
    let value = tree
        .get(12345)?
        .expect("Value not found")
        .decode()
        .expect("Decoding failed");
    assert_eq!(value, 42);
    Ok(())
}

#[test]
fn test_u128_str_encoder() -> sled::Result<()> {
    let db = sled::Config::default().temporary(true).open()?;

    // Let's test mixed types, too.
    // uuid -> string is a somewhat realistic combination.

    let tree = TreeWrapper::<BigEndianU128Encoder, StringEncoder>::new(db.open_tree("int_str")?);
    tree.insert(12345, "Value")?;
    let ivec = tree.get(12345)?.expect("Value not found");
    let value = ivec.decode().expect("Decoding failed");
    assert_eq!(value, "Value");
    Ok(())
}

/// Encode and Decode arbitrary stuff as JSON. MessagePack or CBOR may be more suitable.
struct JSONEncoder<T>(std::marker::PhantomData<T>);
impl<'a, T> Encoder<'a> for JSONEncoder<T>
where
    T: Sized + Serialize + Deserialize<'a>,
    T: 'a,
{
    type In = &'a T;
    type Encoded = Vec<u8>;
    type Out = T;

    fn encode(d: Self::In) -> Self::Encoded {
        serde_json::to_vec(&d).unwrap()
    }

    fn decode(bytes: &'a [u8]) -> Option<Self::Out> {
        serde_json::from_slice(bytes).unwrap()
    }
}

#[test]
fn test_json_encoder() -> sled::Result<()> {
    let db = sled::Config::default().temporary(true).open()?;

    // Any owned serde type works just fine.

    #[derive(Serialize, Deserialize, PartialEq, Debug)]
    struct TestJSONValue {
        pub name: String,
        pub age: u32,
    }

    let json_value = TestJSONValue {
        name: "Name".to_owned(),
        age: 18,
    };
    // using json in a key is unwise, but let's test it anyway
    let tree = TreeWrapper::<JSONEncoder<TestJSONValue>, JSONEncoder<TestJSONValue>>::new(
        db.open_tree("json_json")?,
    );
    tree.insert(&json_value, &json_value)?;
    let value = tree
        .get(&json_value)?
        .expect("Value not found")
        .decode()
        .expect("Decoding failed");
    assert_eq!(value, json_value);
    Ok(())
}

#[test]
fn test_json_encoder_ref() -> sled::Result<()> {
    let db = sled::Config::default().temporary(true).open()?;

    // serde allows zero copy deserialization for certain formats.

    // Unfortunately, I haven't found a way to make the Encoder generic yet.
    // The issue is that T is a T<'a>, and I don't know how to specify that it's the same lifetime as on the Encoder.
    // This example uses a non-generic Encoder instead.

    #[derive(Serialize, Deserialize, PartialEq, Debug)]
    struct TestJSONValueWithRef<'a> {
        pub name: &'a str,
        pub age: u32,
    }

    struct JSONEncoderRef();
    impl<'a> Encoder<'a> for JSONEncoderRef {
        type In = &'a TestJSONValueWithRef<'a>;
        type Encoded = Vec<u8>;
        type Out = TestJSONValueWithRef<'a>;

        fn encode(d: Self::In) -> Self::Encoded {
            serde_json::to_vec(&d).unwrap()
        }

        fn decode(bytes: &'a [u8]) -> Option<Self::Out> {
            serde_json::from_slice(bytes).unwrap()
        }
    }

    #[derive(Serialize, Deserialize, PartialEq, Debug)]
    struct TestJSONValue {
        pub name: String,
        pub age: u32,
    }

    let json_value_with_ref = TestJSONValueWithRef {
        name: "Name",
        age: 18,
    };
    let tree =
        TreeWrapper::<BigEndianU128Encoder, JSONEncoderRef>::new(db.open_tree("int_jsonref")?);
    tree.insert(42, &json_value_with_ref)?;
    let res = tree.get(42)?.expect("Value not found");
    let value = res.decode().expect("Decoding failed");
    assert_eq!(value, json_value_with_ref);
    Ok(())
}

/// Encoding and decoding types made using the zerocopy crate
struct ZeroCopyEncoder<T>(std::marker::PhantomData<T>);
impl<'a, T> Encoder<'a> for ZeroCopyEncoder<T>
where
    T: FromBytes + AsBytes + Unaligned,
    T: 'a,
{
    type In = &'a T;
    type Encoded = &'a [u8];
    type Out = &'a T;

    fn encode(d: Self::In) -> Self::Encoded {
        d.as_bytes()
    }

    fn decode(bytes: &'a [u8]) -> Option<Self::Out> {
        let layout: LayoutVerified<&[u8], T> = LayoutVerified::new_unaligned(bytes)?;
        Some(layout.into_ref())
    }
}

#[test]
fn test_zerocopy_encoder() -> sled::Result<()> {
    use byteorder::{BigEndian, LittleEndian};
    use zerocopy::byteorder::U64;

    let db = sled::Config::default().temporary(true).open()?;

    // Same types as used by the structured example at
    // https://github.com/spacejam/sled/blob/master/examples/structured.rs
    #[derive(FromBytes, AsBytes, Unaligned)]
    #[repr(C)]
    struct Key {
        a: U64<BigEndian>,
        b: U64<BigEndian>,
    }
    #[derive(FromBytes, AsBytes, Unaligned, PartialEq, Debug)]
    #[repr(C)]
    struct Value {
        count: U64<LittleEndian>,
        whatever: [u8; 16],
    }

    let key = Key {
        a: U64::new(21),
        b: U64::new(890),
    };
    let value = Value {
        count: U64::new(0),
        whatever: [0; 16],
    };
    let tree =
        TreeWrapper::<ZeroCopyEncoder<Key>, ZeroCopyEncoder<Value>>::new(db.open_tree("zerocopy")?);
    tree.insert(&key, &value)?;
    let res = tree.get(&key)?.expect("Value not found");
    let value2 = res.decode().expect("Decoding failed");
    assert_eq!(&value, value2);
    Ok(())
}

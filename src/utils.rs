use num_bigint::BigUint as big_uint;
use num_traits::Zero;
use std::ops::Shl;

#[cfg(feature = "kzg")]
use crate::halo2::arithmetic::BaseExt as Field;
#[cfg(feature = "zcash")]
use crate::halo2::arithmetic::FieldExt as Field;

pub fn big_to_fe<F: Field>(e: big_uint) -> F {
    #[cfg(feature = "zcash")]
    {
        F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
    }
    #[cfg(feature = "kzg")]
    {
        let mut bytes = e.to_bytes_le();
        bytes.resize(32, 0);
        let mut bytes = &bytes[..];
        F::read(&mut bytes).unwrap()
    }
}

pub fn fe_to_big<F: Field>(fe: F) -> big_uint {
    #[cfg(feature = "zcash")]
    {
        big_uint::from_bytes_le(fe.to_repr().as_ref())
    }
    #[cfg(feature = "kzg")]
    {
        let mut bytes: Vec<u8> = Vec::new();
        fe.write(&mut bytes).unwrap();
        big_uint::from_bytes_le(&bytes[..])
    }
}

pub fn decompose<F: Field>(e: F, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
    decompose_big(fe_to_big(e), number_of_limbs, bit_len)
}

pub fn decompose_big<F: Field>(e: big_uint, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
    let mut e = e;
    let mask = big_uint::from(1usize).shl(bit_len) - 1usize;
    let limbs: Vec<F> = (0..number_of_limbs)
        .map(|_| {
            let limb = mask.clone() & e.clone();
            e = e.clone() >> bit_len;
            big_to_fe(limb)
        })
        .collect();

    limbs
}

pub fn compose(input: Vec<big_uint>, bit_len: usize) -> big_uint {
    let mut e = big_uint::zero();
    for (i, limb) in input.iter().enumerate() {
        e += limb << (bit_len * i)
    }
    e
}

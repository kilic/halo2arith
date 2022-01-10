use halo2::arithmetic::FieldExt;
use num_bigint::BigUint as big_uint;
use std::ops::Shl;

pub fn big_to_fe<F: FieldExt>(e: big_uint) -> F {
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

pub fn fe_to_big<F: FieldExt>(fe: F) -> big_uint {
    big_uint::from_bytes_le(fe.to_repr().as_ref())
}

pub fn decompose<F: FieldExt>(e: F, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
    decompose_big(fe_to_big(e), number_of_limbs, bit_len)
}

pub fn decompose_big<F: FieldExt>(e: big_uint, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
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

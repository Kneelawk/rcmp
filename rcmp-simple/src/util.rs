// util.rs - Contains utility functions for helping the different computations.
//
// Copyright (C) 2021  Jed Pommert (Kneelawk)
//
// This file is part of rcmp-simple.
//
// rcmp-simple is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// rcmp-simple is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

/// Adds the multiprecision number `a` the the multiprecision number `b`,
/// storing the result into `into` and returning true if a carry is required.
#[inline]
pub fn add_n_into<const PRECISION: usize>(
    a: &[u32; PRECISION],
    b: &[u32; PRECISION],
    into: &mut [u32; PRECISION],
) -> bool {
    // This implementation is practically identical to the one in GMP.
    let mut carry = 0u32;
    let (mut start, mut mid, mut res): (u32, u32, u32);

    for i in (0..PRECISION).rev() {
        start = a[i];
        mid = start.wrapping_add(b[i]);
        res = mid.wrapping_add(carry);
        carry = (mid < start) as u32 | (res < mid) as u32;
        into[i] = res;
    }

    carry != 0
}

/// Adds the multiprecision number `a` to the multiprecision number `b`, storing
/// the result into `a` and returning true if a carry is required.
#[inline]
pub fn add_n_mut<const PRECISION: usize>(a: &mut [u32; PRECISION], b: &[u32; PRECISION]) -> bool {
    // This implementation is practically identical to the one in GMP.
    let mut carry = 0u32;
    let (mut start, mut mid, mut res): (u32, u32, u32);

    for i in (0..PRECISION).rev() {
        start = a[i];
        mid = start.wrapping_add(b[i]);
        res = mid.wrapping_add(carry);
        carry = (mid < start) as u32 | (res < mid) as u32;
        a[i] = res;
    }

    carry != 0
}

/// Subtracts the multiprecision number `b` from the multiprecision number `a`,
/// storing the result into `into` and returning true if a borrow is required.
#[inline]
pub fn sub_n_into<const PRECISION: usize>(
    a: &[u32; PRECISION],
    b: &[u32; PRECISION],
    into: &mut [u32; PRECISION],
) -> bool {
    // This implementation is practically identical to the one in GMP.
    let mut borrow = 0u32;
    let (mut start, mut mid, mut res): (u32, u32, u32);

    for i in (0..PRECISION).rev() {
        start = a[i];
        mid = start.wrapping_sub(b[i]);
        res = mid.wrapping_sub(borrow);
        borrow = (mid > start) as u32 | (res > mid) as u32;
        into[i] = res;
    }

    borrow != 0
}

/// Subtracts the multiprecision number `b` from the multiprecision number `a`,
/// storing the result into `a` and returning true if a borrow is required.
#[inline]
pub fn sub_n_mut<const PRECISION: usize>(a: &mut [u32; PRECISION], b: &[u32; PRECISION]) -> bool {
    // This implementation is practically identical to the one in GMP.
    let mut borrow = 0u32;
    let (mut start, mut mid, mut res): (u32, u32, u32);

    for i in (0..PRECISION).rev() {
        start = a[i];
        mid = start.wrapping_sub(b[i]);
        res = mid.wrapping_sub(borrow);
        borrow = (mid > start) as u32 | (res > mid) as u32;
        a[i] = res;
    }

    borrow != 0
}

/// Subtracts the multiprecision number `b` from the multiprecision number `a`,
/// storing the result into `b` and returning true if a borrow is required.
#[inline]
pub fn sub_n_mut_2<const PRECISION: usize>(a: &[u32; PRECISION], b: &mut [u32; PRECISION]) -> bool {
    // This implementation is practically identical to the one in GMP.
    let mut borrow = 0u32;
    let (mut start, mut mid, mut res): (u32, u32, u32);

    for i in (0..PRECISION).rev() {
        start = a[i];
        mid = start.wrapping_sub(b[i]);
        res = mid.wrapping_sub(borrow);
        borrow = (mid > start) as u32 | (res > mid) as u32;
        b[i] = res;
    }

    borrow != 0
}

/// This function multiplies two `u32`s together to get the high and low 32-bit
/// words of the 64-bit result.
///
/// # Returns
/// This returns `u32` in the order (`high`, `low`).
#[inline]
pub fn mul_hi_low(a: u32, b: u32) -> (u32, u32) {
    // We perform this multiplication without using `u64`s by breaking each `u32` up
    // into two 16-bit pieces and multiplying those.

    let al = a & 0xFFFF;
    let ah = (a >> 0x10) & 0xFFFF;
    let bl = b & 0xFFFF;
    let bh = (b >> 0x10) & 0xFFFF;

    let mid1 = ah * bl;
    let mid2 = al * bh;

    let low = al * bl;
    let low2 = low.wrapping_add((mid1 & 0xFFFF) << 0x10);
    let low3 = low2.wrapping_add((mid2 & 0xFFFF) << 0x10);
    let high = ah * bh
        + ((mid1 >> 0x10) & 0xFFFF)
        + ((mid2 >> 0x10) & 0xFFFF)
        + (low2 < low) as u32
        + (low3 < low2) as u32;

    (high, low3)
}

/// Multiplies the multiprecision number `a` by the single-precision number `b`,
/// storing the result into `into` and returning the overflow.
#[inline]
pub fn mul_1<const PRECISION: usize>(
    a: &[u32; PRECISION],
    b: u32,
    into: &mut [u32; PRECISION],
    into_offset: isize,
) -> u32 {
    // Here, we're adding up every limb multiplied by `b`.
    let mut carry = 0u32;
    for i in (0..PRECISION).rev() {
        // We only care about part of the multiplication result, so we add the index
        // offset and only evaluate the areas where the new index is valid.
        let k = i as isize + into_offset;
        if k >= 0 && k < PRECISION as isize {
            let k = k as usize;

            // Perform the multiplication.
            let (t_high, t_low) = mul_hi_low(a[i], b);

            // Add the carry.
            let t_low2 = t_low.wrapping_add(carry);

            // Next we assign the least-significant 32 bits into the current limb and
            // carry everything left over to the next limb.
            carry = t_high + (t_low2 < t_low) as u32;
            into[k] = t_low2;
        }
    }

    // Return the carry.
    carry
}

/// Multiplies the multiprecision number `a` by the single-precision number
/// `b`, adding the result into `into` and returning the overflow.
#[inline]
pub fn addmul_1<const PRECISION: usize>(
    a: &[u32; PRECISION],
    b: u32,
    into: &mut [u32; PRECISION],
    into_offset: isize,
) -> u32 {
    // Here, we're adding up every limb multiplied by `b`.
    let mut carry = 0u32;
    for i in (0..PRECISION).rev() {
        // We only care about part of the multiplication result, so we add the index
        // offset and only evaluate the areas where the new index is valid.
        let k = i as isize + into_offset;
        if k >= 0 && k < PRECISION as isize {
            let k = k as usize;

            // Perform the multiplication.
            let (t_high, t_low) = mul_hi_low(a[i], b);

            // Add anything else that was already in this limb. This is how carries
            // work across outer multiplication loops.
            let t_low2 = t_low.wrapping_add(into[k]);
            let t_high2 = t_high + (t_low2 < t_low) as u32;

            // Add the carry.
            let t_low3 = t_low2.wrapping_add(carry);

            // Next we assign the least-significant 32 bits into the current limb and
            // carry everything left over to the next limb.
            carry = t_high2 + (t_low3 < t_low2) as u32;
            into[k] = t_low3;
        }
    }

    // Return the carry.
    carry
}

/// Multiplies the multiprecision number `a` by the single-precision number `b`,
/// storing the result into `into` and returning the carry word.
///
/// This variant is designed to store the entire results of multiplication, not
/// just the least-significant results. This means that the carry word for
/// multiplication when `b` is an MSW should always be 0.
#[inline]
pub fn addmul_1_full<const PRECISION: usize>(
    a: &[u32; PRECISION],
    b: u32,
    into: &mut [u32; PRECISION * 2],
    into_offset: usize,
) -> u32 {
    // This should never happen so let's make an assertion that should hopefully
    // show us if something is broken during unit-testing.
    debug_assert!(
        into_offset <= PRECISION,
        "into_offset should always be less or equal than PRECISION"
    );

    // Here, we're adding up every limb multiplied by `b`.
    let mut carry = 0u32;
    for i in (0..PRECISION).rev() {
        let k = i + into_offset;

        // Perform the multiplication.
        let (t_high, t_low) = mul_hi_low(a[i], b);

        // Add anything else that was already in this limb. This is how carries
        // work across outer multiplication loops.
        let t_low2 = t_low.wrapping_add(into[k]);
        let t_high2 = t_high + (t_low2 < t_low) as u32;

        // Add the carry.
        let t_low3 = t_low2.wrapping_add(carry);

        // Next we assign the least-significant 32 bits into the current limb and
        // carry everything left over to the next limb.
        carry = t_high2 + (t_low3 < t_low2) as u32;
        into[k] = t_low3;
    }

    // Return the carry.
    carry
}

/// Compares `a` to `b`, returning `1` if `a` is bigger, `0` if `a` and `b` are
/// equal, and `-1` if `b` is bigger.
#[inline]
pub fn cmp<const PRECISION: usize>(a: &[u32; PRECISION], b: &[u32; PRECISION]) -> i32 {
    for i in 0..PRECISION {
        let al = a[i];
        let bl = b[i];
        if al != bl {
            return if al > bl { 1 } else { -1 };
        }
    }

    0
}

/// Sets `a` to zero.
#[inline]
pub fn zero<const PRECISION: usize>(a: &mut [u32; PRECISION]) {
    for i in 0..PRECISION {
        a[i] = 0;
    }
}

#[cfg(test)]
mod tests {
    use crate::util::mul_hi_low;

    #[test]
    fn test_mul_hi_low() {
        let (high, low) = mul_hi_low(0xFFFFFFFF, 0xFFFFFFFF);

        assert_eq!(low, 0x00000001, "Low should be 0x00000001");
        assert_eq!(high, 0xFFFFFFFE, "High should be 0xFFFFFFFE");
    }
}

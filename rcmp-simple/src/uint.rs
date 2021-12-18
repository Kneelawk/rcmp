// uint.rs - Contains implementation of unsigned integer multiprecision
// arithmetic.
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

use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

use crate::util::mul_hi_low;

/// Unsigned integer extended fixed precision implementation.
///
/// This only holds positive integers or 0. This struct is generic over
/// precision. All operations are precision-consistent, returning unsigned
/// integers with the same precision as that of the inputs.
///
/// # Example
/// ```rust
/// # use rcmp_simple::UInt;
/// let num = UInt::new([0, 0xFFFFFFFE]);
/// let sum = num + UInt::new([0, 3]);
///
/// assert_eq!(sum, UInt::new([1, 1]));
/// ```
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct UInt<const PRECISION: usize> {
    /// Numbers are stored with the most significant limb first (at the smallest
    /// index) and the least significant limb last (at the largest index).
    limbs: [u32; PRECISION],
}

impl<const PRECISION: usize> UInt<PRECISION> {
    /// Creates a new unsigned integer with the given limbs.
    ///
    /// Numbers in the limbs are stored with the most significant limb first (at
    /// the smallest index) and the least significant limb last (at the largest
    /// index).
    pub fn new(limbs: [u32; PRECISION]) -> UInt<PRECISION> {
        UInt { limbs }
    }

    /// Adds `self` and `rhs`, storing the sum into `into`, returning `true` if
    /// an overflow occured.
    ///
    /// # Example
    /// ```rust
    /// # use rcmp_simple::UInt;
    /// let num = UInt::new([0xFFFFFFFF, 0xFFFFFFFE]);
    /// let mut sum = UInt::new([0; 2]);
    /// let overflow = num.overflowing_add_into(&UInt::new([0, 3]), &mut sum);
    ///
    /// assert_eq!(sum, UInt::new([0, 1]));
    /// assert!(overflow);
    /// ```
    pub fn overflowing_add_into(&self, rhs: &UInt<PRECISION>, into: &mut UInt<PRECISION>) -> bool {
        // This implementation is practically identical to the one in GMP.
        let mut carry = 0u32;
        let (mut start, mut mid, mut res): (u32, u32, u32);

        for i in (0..PRECISION).rev() {
            start = self.limbs[i];
            mid = start.wrapping_add(rhs.limbs[i]);
            res = mid.wrapping_add(carry);
            carry = (mid < start) as u32 | (res < mid) as u32;
            into.limbs[i] = res;
        }

        carry != 0
    }

    /// Adds `self` and `rhs`, storing the sum into `self, returning `true` if
    /// an overflow occurred.
    ///
    /// # Example
    /// ```rust
    /// # use rcmp_simple::UInt;
    /// let mut num = UInt::new([0xFFFFFFFF, 0xFFFFFFFE]);
    /// let overflow = num.overflowing_add_mut(&UInt::new([0, 3]));
    ///
    /// assert_eq!(num, UInt::new([0, 1]));
    /// assert!(overflow);
    /// ```
    pub fn overflowing_add_mut(&mut self, rhs: &UInt<PRECISION>) -> bool {
        // This implementation is practically identical to the one in GMP.
        let mut carry = 0u32;
        let (mut start, mut mid, mut res): (u32, u32, u32);

        for i in (0..PRECISION).rev() {
            start = self.limbs[i];
            mid = start.wrapping_add(rhs.limbs[i]);
            res = mid.wrapping_add(carry);
            carry = (mid < start) as u32 | (res < mid) as u32;
            self.limbs[i] = res;
        }

        carry != 0
    }

    /// Subtracts `rhs` from `self`, storing the difference into `into`,
    /// returning `true` if an underflow occurred.
    ///
    /// # Examples
    /// ```rust
    /// # use rcmp_simple::UInt;
    /// let num = UInt::new([1, 0]);
    /// let mut dif = UInt::new([0; 2]);
    /// let underflow = num.overflowing_sub_into(&UInt::new([0, 1]), &mut dif);
    ///
    /// assert_eq!(dif, UInt::new([0, 0xFFFFFFFF]));
    /// assert!(!underflow);
    /// ```
    ///
    /// An example of when an underflow might occur:
    /// ```rust
    /// # use rcmp_simple::UInt;
    /// let num = UInt::new([0, 1]);
    /// let mut dif = UInt::new([0; 2]);
    /// let underflow = num.overflowing_sub_into(&UInt::new([0, 2]), &mut dif);
    ///
    /// assert_eq!(dif, UInt::new([0xFFFFFFFF, 0xFFFFFFFF]));
    /// assert!(underflow);
    /// ```
    pub fn overflowing_sub_into(&self, rhs: &UInt<PRECISION>, into: &mut UInt<PRECISION>) -> bool {
        // This implementation is practically identical to the one in GMP.
        let mut borrow = 0u32;
        let (mut start, mut mid, mut res): (u32, u32, u32);

        for i in (0..PRECISION).rev() {
            start = self.limbs[i];
            mid = start.wrapping_sub(rhs.limbs[i]);
            res = mid.wrapping_sub(borrow);
            borrow = (mid > start) as u32 | (res > mid) as u32;
            into.limbs[i] = res;
        }

        borrow != 0
    }

    /// Subtracts `rhs` from `self`, storing the difference into `self`,
    /// returning `true` if an underflow occurred.
    ///
    /// # Examples
    /// ```rust
    /// # use rcmp_simple::UInt;
    /// let mut num = UInt::new([0, 1]);
    /// let underflow = num.overflowing_sub_mut(&UInt::new([0, 2]));
    ///
    /// assert_eq!(num, UInt::new([0xFFFFFFFF, 0xFFFFFFFF]));
    /// assert!(underflow);
    /// ```
    pub fn overflowing_sub_mut(&mut self, rhs: &UInt<PRECISION>) -> bool {
        // This implementation is practically identical to the one in GMP.
        let mut borrow = 0u32;
        let (mut start, mut mid, mut res): (u32, u32, u32);

        for i in (0..PRECISION).rev() {
            start = self.limbs[i];
            mid = start.wrapping_sub(rhs.limbs[i]);
            res = mid.wrapping_sub(borrow);
            borrow = (mid > start) as u32 | (res > mid) as u32;
            self.limbs[i] = res;
        }

        borrow != 0
    }

    /// Multiplies `rhs` by `self`, storing the lower half of the result into
    /// `into`, returning true if the upper half of the result would be
    /// non-zero.
    ///
    /// # Examples
    /// ```rust
    /// # use rcmp_simple::UInt;
    /// let num = UInt::new([0, 0xFFFFFFFF]);
    /// let mut prod = UInt::new([0; 2]);
    /// let overflow = num.overflowing_mul_into(&UInt::new([0, 0xFFFFFFFF]), &mut prod);
    ///
    /// assert_eq!(prod, UInt::new([0xFFFFFFFE, 0x00000001]));
    /// assert!(!overflow);
    /// ```
    ///
    /// An example of when an overflow might occur:
    /// ```rust
    /// # use rcmp_simple::UInt;
    /// let num = UInt::new([0xFFFFFFFF, 0xFFFFFFFF]);
    /// let mut prod = UInt::new([0; 2]);
    /// let overflow = num.overflowing_mul_into(&UInt::new([0xFFFFFFFF, 0xFFFFFFFF]), &mut prod);
    ///
    /// assert_eq!(prod, UInt::new([0x00000000, 0x00000001]));
    /// assert!(overflow);
    /// ```
    pub fn overflowing_mul_into(&self, rhs: &UInt<PRECISION>, into: &mut UInt<PRECISION>) -> bool {
        let mut overflow = false;

        for j in (0..PRECISION).rev() {
            let b = rhs.limbs[j];

            // Here, we're multiplying everything by `b` so if `b == 0` then nothing is
            // happening, so let's just skip it entirely.
            if b != 0 {
                // Here, we're adding up every limb multiplied by `b`.
                let mut carry = 0u32;
                for i in (0..PRECISION).rev() {
                    // We only care about the lower half of the multiplication, so we only calculate
                    // this if `i + j` refer to the less-significant (higher-index) half.
                    let k = i + j;
                    if k >= (PRECISION - 1) {
                        // The `into` int should only contain the less-significant half, so the
                        // index into it is the index into the less-significant half.
                        let k = k - (PRECISION - 1);
                        let (mut t_high, t_low) = mul_hi_low(self.limbs[i], b);

                        // Add anything else that was already in this limb. This is how carries work
                        // across `j` values.
                        let t_low2 = t_low.wrapping_add(into.limbs[k]);
                        t_high += (t_low2 < t_low) as u32;

                        // Add the carry.
                        let t_low3 = t_low2.wrapping_add(carry);
                        t_high += (t_low3 < t_low2) as u32;

                        // Next we assign the least-significant 32 bits into the current limb and
                        // carry everything left over to the next limb.
                        carry = t_high;
                        into.limbs[k] = t_low3;
                    }
                }
                overflow |= carry != 0;
            }
        }

        overflow
    }
}

impl<const PRECISION: usize> Add for UInt<PRECISION> {
    type Output = Self;

    /// Performs the `+` operation.
    ///
    /// # Panics
    /// This function panics if an overflow occurs and debug assertions are
    /// enabled. Otherwise, this function will wrap.
    fn add(self, rhs: Self) -> Self::Output {
        let mut res = UInt::new([0; PRECISION]);
        let overflow = self.overflowing_add_into(&rhs, &mut res);
        debug_assert!(!overflow, "Add overflowed");
        res
    }
}

impl<const PRECISION: usize> Sub for UInt<PRECISION> {
    type Output = Self;

    /// Performs the `-` operation.
    ///
    /// # Panics
    /// This function panics if an underflow occurs and debug assertions are
    /// enabled. Otherwise, this function will wrap.
    fn sub(self, rhs: Self) -> Self::Output {
        let mut res = UInt::new([0; PRECISION]);
        let underflow = self.overflowing_sub_into(&rhs, &mut res);
        debug_assert!(!underflow, "Subtract underflowed");
        res
    }
}

impl<const PRECISION: usize> Mul for UInt<PRECISION> {
    type Output = Self;

    /// Performs the `*` operation.
    ///
    /// # Panics
    /// This function panics if an overflow occurs and debug assertions are
    /// enabled. Otherwise, this function will wrap.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut res = UInt::new([0; PRECISION]);
        let overflow = self.overflowing_mul_into(&rhs, &mut res);
        debug_assert!(!overflow, "Multiply overflowed");
        res
    }
}

impl<const PRECISION: usize> AddAssign for UInt<PRECISION> {
    /// Performs the `+=` operation.
    ///
    /// # Panics
    /// This function panics if an overflow occurs and debug assertions are
    /// enabled. Otherwise, this function will wrap.
    fn add_assign(&mut self, rhs: Self) {
        let overflow = self.overflowing_add_mut(&rhs);
        debug_assert!(!overflow, "Add overflowed");
    }
}

impl<const PRECISION: usize> SubAssign for UInt<PRECISION> {
    /// Performs the `-=` operation.
    ///
    /// # Panics
    /// This function panics if an underflow occurs and debug assertions are
    /// enabled. Otherwise this function will wrap.
    fn sub_assign(&mut self, rhs: Self) {
        let underflow = self.overflowing_sub_mut(&rhs);
        debug_assert!(!underflow, "Subtract underflowed");
    }
}

impl<const PRECISION: usize> MulAssign for UInt<PRECISION> {
    /// Performs the `*=` operation.
    ///
    /// # Panics
    /// This function panics if an overflow occurs and debug assertions are
    /// enabled. Otherwise this function will wrap.
    fn mul_assign(&mut self, rhs: Self) {
        let mut res = UInt::new([0; PRECISION]);
        let overflow = self.overflowing_mul_into(&rhs, &mut res);
        debug_assert!(!overflow, "Multiply overflowed");
        *self = res;
    }
}

#[cfg(test)]
mod tests {
    use super::UInt;

    #[test]
    fn normal_add() {
        let num = UInt::new([0, 1]);
        let sum = num + UInt::new([0, 2]);
        assert_eq!(sum, UInt::new([0, 3]), "The result must be [0, 3]");
    }

    #[test]
    fn multi_precision_add() {
        let num = UInt::new([0, 0xFFFFFFFE]);
        let sum = num + UInt::new([0, 3]);

        assert_eq!(sum, UInt::new([1, 1]), "The result must be [1, 1]");
    }

    #[test]
    fn multi_precision_overflowing_add() {
        let num = UInt::new([0xFFFFFFFF, 0xFFFFFFFE]);
        let mut sum = UInt::new([0; 2]);
        let overflow = num.overflowing_add_into(&UInt::new([0, 3]), &mut sum);

        assert_eq!(sum, UInt::new([0, 1]), "The result must be [0, 1]");
        assert!(overflow, "There must be overflow");
    }

    #[test]
    fn multi_precision_carry_add() {
        let num = UInt::new([0, 0, 1]);
        let sum = num + UInt::new([0, 0xFFFFFFFF, 0xFFFFFFFF]);

        assert_eq!(sum, UInt::new([1, 0, 0]), "The result must be [1, 0, 0]");
    }

    #[test]
    fn normal_sub() {
        let num = UInt::new([0, 3]);
        let dif = num - UInt::new([0, 2]);

        assert_eq!(dif, UInt::new([0, 1]));
    }

    #[test]
    fn multi_precision_borrow_sub() {
        let num = UInt::new([1, 0, 0]);
        let dif = num - UInt::new([0, 0, 1]);

        assert_eq!(
            dif,
            UInt::new([0, 0xFFFFFFFF, 0xFFFFFFFF]),
            "The result should be [0, 0xFFFFFFFF, 0xFFFFFFFF]"
        );
    }

    #[test]
    fn normal_mul() {
        let num = UInt::new([0, 2]);
        let prod = num * UInt::new([0, 3]);

        assert_eq!(prod, UInt::new([0, 6]), "The result should be [0, 6]");

        let mut num = UInt::new([0, 2]);
        num *= UInt::new([0, 3]);

        assert_eq!(num, UInt::new([0, 6]), "The result should be [0, 6]");
    }

    #[test]
    fn four_precision_mul() {
        let num = UInt::new([0, 0, 0xFFFFFFFF, 0xFFFFFFFF]);
        let prod = num.clone() * num;

        assert_eq!(
            prod,
            UInt::new([0xFFFFFFFF, 0xFFFFFFFE, 0x00000000, 0x00000001]),
            "The result should be [0xFFFFFFFF, 0xFFFFFFFE, 0x00000000, 0x00000001]"
        );
    }

    #[test]
    fn four_precision_mul_2() {
        let num = UInt::new([0, 0, 0xFFFFFFFF, 0]);
        let prod = num.clone() * num;

        assert_eq!(
            prod,
            UInt::new([0xFFFFFFFE, 0x00000001, 0, 0]),
            "The result should be [0xFFFFFFFE, 0x00000001, 0x00000000, 0x00000000]"
        );
    }
}

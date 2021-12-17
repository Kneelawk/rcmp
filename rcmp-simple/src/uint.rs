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

use std::ops::Add;

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
    /// Creates a new natural number with the given limbs.
    ///
    /// Numbers in the limbs are stored with the most significant limb first (at
    /// the smallest index) and the least significant limb last (at the largest
    /// index).
    pub fn new(limbs: [u32; PRECISION]) -> UInt<PRECISION> {
        UInt { limbs }
    }

    /// Adds `self` and `rhs` returning a new natural number that is the sum of
    /// these two numbers.
    ///
    /// # Example
    /// ```rust
    /// # use rcmp_simple::UInt;
    /// let num = UInt::new([0xFFFFFFFF, 0xFFFFFFFE]);
    /// let (sum, overflow) = num.overflowing_add(&UInt::new([0, 3]));
    ///
    /// assert_eq!(sum, UInt::new([0, 1]));
    /// assert!(overflow);
    /// ```
    pub fn overflowing_add(&self, rhs: &UInt<PRECISION>) -> (UInt<PRECISION>, bool) {
        // This implementation is practically identical to the one in GMP.
        let mut limbs = [0u32; PRECISION];
        let mut carry = 0u32;

        let (mut a, mut b, mut mid, mut res);

        for i in (0..PRECISION).rev() {
            a = self.limbs[i];
            b = rhs.limbs[i];
            mid = a.wrapping_add(b);
            res = mid.wrapping_add(carry);
            carry = (mid < a) as u32 | (res < mid) as u32;
            limbs[i] = res;
        }

        (UInt { limbs }, carry != 0)
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
        let (res, overflow) = self.overflowing_add(&rhs);
        debug_assert!(!overflow, "Add overflowed");
        res
    }
}

#[cfg(test)]
mod tests {
    use super::UInt;

    #[test]
    fn normal_add() {
        let num = UInt::new([0, 1]);
        let new_num = num + UInt::new([0, 2]);
        assert_eq!(new_num, UInt::new([0, 3]), "The result must be [0, 3]");
    }

    #[test]
    fn multi_precision_add() {
        let num = UInt::new([0, 0xFFFFFFFE]);
        let new_num = num + UInt::new([0, 3]);

        assert_eq!(new_num, UInt::new([1, 1]), "The result must be [1, 1]");
    }

    #[test]
    fn multi_precision_overflowing_add() {
        let num = UInt::new([0xFFFFFFFF, 0xFFFFFFFE]);
        let (new_num, overflow) = num.overflowing_add(&UInt::new([0, 3]));

        assert_eq!(new_num, UInt::new([0, 1]), "The result must be [0, 1]");
        assert!(overflow, "There must be overflow");
    }

    #[test]
    fn multi_precision_carry_add() {
        let num = UInt::new([0, 0, 1]);
        let sum = num + UInt::new([0, 0xFFFFFFFF, 0xFFFFFFFF]);

        assert_eq!(sum, UInt::new([1, 0, 0]), "The result must be [1, 0, 0]");
    }
}

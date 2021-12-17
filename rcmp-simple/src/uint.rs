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

/// Natural number extended fixed precision implementation.
///
/// This only holds positive integers or 0. This struct is generic over
/// precision. All operations are precision-consistent, returning natural
/// numbers with the same precision as that of the inputs.
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct UnsignedInteger<const PRECISION: usize> {
    /// Numbers are stored with the most significant limb first (at the smallest
    /// index) and the least significant limb last (at the largest index).
    limbs: [u32; PRECISION],
}

impl<const PRECISION: usize> UnsignedInteger<PRECISION> {
    /// Creates a new natural number with the given limbs.
    ///
    /// Numbers in the limbs are stored with the most significant limb first (at
    /// the smallest index) and the least significant limb last (at the largest
    /// index).
    pub fn new(limbs: [u32; PRECISION]) -> UnsignedInteger<PRECISION> {
        UnsignedInteger { limbs }
    }

    /// Adds `self` and `rhs` returning a new natural number that is the sum of
    /// these two numbers.
    pub fn overflowing_add(
        &self,
        rhs: &UnsignedInteger<PRECISION>,
    ) -> (UnsignedInteger<PRECISION>, bool) {
        let mut limbs = [0u32; PRECISION];
        let mut carry = false;

        for i in (0..PRECISION).rev() {
            limbs[i] = self.limbs[i]
                .wrapping_add(rhs.limbs[i])
                .wrapping_add(if carry { 1 } else { 0 });
            carry = limbs[i] < self.limbs[i];
        }

        (UnsignedInteger { limbs }, carry)
    }
}

impl<const PRECISION: usize> Add for UnsignedInteger<PRECISION> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let (res, overflow) = self.overflowing_add(&rhs);
        debug_assert!(!overflow, "Add overflowed");
        res
    }
}

#[cfg(test)]
mod tests {
    use super::UnsignedInteger;

    #[test]
    fn normal_add() {
        let num = UnsignedInteger::new([0, 1]);
        let new_num = num + UnsignedInteger::new([0, 2]);
        assert_eq!(
            new_num,
            UnsignedInteger::new([0, 3]),
            "The result must be [0, 3]"
        );
    }

    #[test]
    fn multi_precision_add() {
        let num = UnsignedInteger::new([0, 0xFFFFFFFE]);
        let new_num = num + UnsignedInteger::new([0, 3]);

        assert_eq!(
            new_num,
            UnsignedInteger::new([1, 1]),
            "The result must be [1, 1]"
        );
    }

    #[test]
    fn multi_precision_overflowing_add() {
        let num = UnsignedInteger::new([0xFFFFFFFF, 0xFFFFFFFE]);
        let (new_num, overflow) = num.overflowing_add(&UnsignedInteger::new([0, 3]));

        assert_eq!(
            new_num,
            UnsignedInteger::new([0, 1]),
            "The result must be [0, 1]"
        );
        assert!(overflow, "There must be overflow");
    }
}

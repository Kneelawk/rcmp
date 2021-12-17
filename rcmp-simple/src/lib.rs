//! # About
//! This library is a simple concept implementation of multiprecision algorithms
//! in rust. The name RCMP stands for Rust Concept Multi-Precision. This library
//! is called a multiprecision library, however, the intended use of this
//! library is actually just to provide expanded, fixed precision types.
//!
//! This library is intended for use in a fractal generator. These
//! implementations are designed to allow me to understand the mechanisms of
//! multiprecision to allow me to implement it in WGSL for the GPU.
//!
//! # Implementation Basis
//! These types and algorithms are implemented based on:
//! * Donald E. Knuth, “The Art of Computer Programming”, volume 2,
//!   “Seminumerical Algorithms”, 1st edition, Addison-Wesley, 1969.
//! * The source code of the GNU MP library as of 2022.
//!
//! # Examples
//! As content is added to this library, doctest examples will be added here.

use std::ops::Add;

/// Natural number extended fixed precision implementation. This only holds
/// positive integers or 0. This struct is generic over precision. All
/// operations are precision-consistent, returning natural numbers with the same
/// precision as that of the inputs.
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
    use crate::UnsignedInteger;

    #[test]
    fn normal_overflowing_add() {
        let num = UnsignedInteger::new([0, 1]);
        let (new_num, overflow) = num.overflowing_add(&UnsignedInteger::new([0, 2]));

        assert_eq!(
            new_num,
            UnsignedInteger::new([0, 3]),
            "The result must be [0, 3]"
        );
        assert!(!overflow, "There must not be any overflow");
    }

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
}

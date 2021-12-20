// udec.rs - Contains implementation of unsigned decimal multiprecision
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

use std::ops::{Add, AddAssign, Sub, SubAssign};

use crate::util::{add_n_into, add_n_mut, sub_n_into, sub_n_mut};

/// Unsigned decimal extended fixed precision implementation with fixed point.
///
/// This holds positive rational numbers or 0 as a series of `u32` limbs instead
/// of as fractions. This struct is generic over precision and the position of
/// its fixed-point. All operations are precision and point consistent,
/// returning unsigned decimals with the same precision and point position as
/// the inputs.
///
/// `PRECISION` is the number of limbs or the number of bits / 32. This means
/// that if `PRECISION == 4` this number would have `4 * 32 = 128` bits.
///
/// `POINT` is the offset of the fixed decimal point in bits from the left-hand
/// side of the number. This means that if `POINT == 4` then the the
/// most-significant bit would represent `8`, the second-most `4`, the
/// third-most `2`, the fourth-most `1`, the fifth-most `0.5`, and so-on.
///
/// # Example
/// ```rust
/// # use rcmp_simple::UDec;
/// let num = UDec::<2, 4>::new([0, 0xFFFFFFFE]);
/// let sum = num + UDec::new([0, 3]);
///
/// assert_eq!(sum, UDec::new([1, 1]));
/// ```
///
/// # Notes
/// Note: `PRECISION` must always be `1` or greater. If `PRECISION == 0` then
/// this object will panic when various methods are called.
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct UDec<const PRECISION: usize, const POINT: u32> {
    limbs: [u32; PRECISION],
}

impl<const PRECISION: usize, const POINT: u32> UDec<PRECISION, POINT> {
    /// Creates a new unsigned decimal with the given limbs.
    ///
    /// Numbers in the limbs are stored with the most significant limb first (at
    /// the smallest index) and the least significant limb last (at the largest
    /// index).
    pub fn new(limbs: [u32; PRECISION]) -> UDec<PRECISION, POINT> {
        UDec { limbs }
    }

    /// Adds `self` and `rhs`, storing the sum into `into`, returning `true` if
    /// an overflow occured.
    ///
    /// # Example
    /// ```rust
    /// # use rcmp_simple::UDec;
    /// let num = UDec::<2, 4>::new([0xFFFFFFFF, 0xFFFFFFFE]);
    /// let mut sum = Default::default();
    /// let overflow = num.overflowing_add_into(&UDec::new([0, 3]), &mut sum);
    ///
    /// assert_eq!(sum, UDec::new([0, 1]));
    /// assert!(overflow);
    /// ```
    pub fn overflowing_add_into(
        &self,
        rhs: &UDec<PRECISION, POINT>,
        into: &mut UDec<PRECISION, POINT>,
    ) -> bool {
        add_n_into(&self.limbs, &rhs.limbs, &mut into.limbs)
    }

    /// Adds `self` and `rhs`, storing the sum into `self, returning `true` if
    /// an overflow occurred.
    ///
    /// # Example
    /// ```rust
    /// # use rcmp_simple::UDec;
    /// let mut num = UDec::<2, 4>::new([0xFFFFFFFF, 0xFFFFFFFE]);
    /// let overflow = num.overflowing_add_mut(&UDec::new([0, 3]));
    ///
    /// assert_eq!(num, UDec::new([0, 1]));
    /// assert!(overflow);
    /// ```
    pub fn overflowing_add_mut(&mut self, rhs: &UDec<PRECISION, POINT>) -> bool {
        add_n_mut(&mut self.limbs, &rhs.limbs)
    }

    /// Subtracts `rhs` from `self`, storing the difference into `into`,
    /// returning `true` if an underflow occurred.
    ///
    /// # Examples
    /// ```rust
    /// # use rcmp_simple::UDec;
    /// let num = UDec::<2, 4>::new([1, 0]);
    /// let mut dif = Default::default();
    /// let underflow = num.overflowing_sub_into(&UDec::new([0, 1]), &mut dif);
    ///
    /// assert_eq!(dif, UDec::new([0, 0xFFFFFFFF]));
    /// assert!(!underflow);
    /// ```
    ///
    /// An example of when an underflow might occur:
    /// ```rust
    /// # use rcmp_simple::UDec;
    /// let num = UDec::<2, 4>::new([0, 1]);
    /// let mut dif = Default::default();
    /// let underflow = num.overflowing_sub_into(&UDec::new([0, 2]), &mut dif);
    ///
    /// assert_eq!(dif, UDec::new([0xFFFFFFFF, 0xFFFFFFFF]));
    /// assert!(underflow);
    /// ```
    pub fn overflowing_sub_into(
        &self,
        rhs: &UDec<PRECISION, POINT>,
        into: &mut UDec<PRECISION, POINT>,
    ) -> bool {
        sub_n_into(&self.limbs, &rhs.limbs, &mut into.limbs)
    }

    /// Subtracts `rhs` from `self`, storing the difference into `self`,
    /// returning `true` if an underflow occurred.
    ///
    /// # Examples
    /// ```rust
    /// # use rcmp_simple::UDec;
    /// let mut num = UDec::<2, 4>::new([0, 1]);
    /// let underflow = num.overflowing_sub_mut(&UDec::new([0, 2]));
    ///
    /// assert_eq!(num, UDec::new([0xFFFFFFFF, 0xFFFFFFFF]));
    /// assert!(underflow);
    /// ```
    pub fn overflowing_sub_mut(&mut self, rhs: &UDec<PRECISION, POINT>) -> bool {
        sub_n_mut(&mut self.limbs, &rhs.limbs)
    }
}

impl<const PRECISION: usize, const POINT: u32> Default for UDec<PRECISION, POINT> {
    fn default() -> Self {
        UDec::new([0; PRECISION])
    }
}

impl<const PRECISION: usize, const POINT: u32> Add for UDec<PRECISION, POINT> {
    type Output = Self;

    /// Performs the `+` operation.
    ///
    /// # Panics
    /// This function panics if an overflow occurs and debug assertions are
    /// enabled. Otherwise, this function will wrap.
    fn add(self, rhs: Self) -> Self::Output {
        let mut res = Default::default();
        let overflow = self.overflowing_add_into(&rhs, &mut res);
        debug_assert!(!overflow, "Add overflowed");
        res
    }
}

impl<const PRECISION: usize, const POINT: u32> Sub for UDec<PRECISION, POINT> {
    type Output = Self;

    /// Performs the `-` operation.
    ///
    /// # Panics
    /// This function panics if an underflow occurs and debug assertions are
    /// enabled. Otherwise, this function will wrap.
    fn sub(self, rhs: Self) -> Self::Output {
        let mut res = Default::default();
        let underflow = self.overflowing_sub_into(&rhs, &mut res);
        debug_assert!(!underflow, "Subtract underflowed");
        res
    }
}

// impl<const PRECISION: usize, const POINT: u32> Mul for UDec<PRECISION, POINT>
// {     type Output = Self;
//
//     /// Performs the `*` operation.
//     ///
//     /// # Panics
//     /// This function panics if an overflow occurs and debug assertions are
//     /// enabled. Otherwise, this function will wrap.
//     fn mul(self, rhs: Self) -> Self::Output {
//         let mut res = Default::default();
//         let overflow = self.overflowing_mul_into(&rhs, &mut res);
//         debug_assert!(!overflow, "Multiply overflowed");
//         res
//     }
// }

impl<const PRECISION: usize, const POINT: u32> AddAssign for UDec<PRECISION, POINT> {
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

impl<const PRECISION: usize, const POINT: u32> SubAssign for UDec<PRECISION, POINT> {
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

// impl<const PRECISION: usize, const POINT: u32> MulAssign for UDec<PRECISION,
// POINT> {     /// Performs the `*=` operation.
//     ///
//     /// # Panics
//     /// This function panics if an overflow occurs and debug assertions are
//     /// enabled. Otherwise this function will wrap.
//     fn mul_assign(&mut self, rhs: Self) {
//         let mut res = Default::default();
//         let overflow = self.overflowing_mul_into(&rhs, &mut res);
//         debug_assert!(!overflow, "Multiply overflowed");
//         *self = res;
//     }
// }

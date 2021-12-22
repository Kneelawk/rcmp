// dec.rs - Contains implementation of signed decimal multiprecision arithmetic.
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

use std::{
    fmt::{Debug, Formatter},
    ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};

use itertools::Itertools;

use crate::util::{
    add_n_into, add_n_mut, addmul_1_full, cmp, sub_n_into, sub_n_mut, sub_n_mut_2, zero,
};

/// Signed decimal extended fixed precision implementation with fixed point.
///
/// This holds signed rational numbers as a series of `u32` limbs instead of as
/// fractions. The sign is held as a separate boolean, indicating if the number
/// is positive. This struct is generic over precision and the position of its
/// fixed-point. All operations are precision and point constant, returning
/// signed decimals with the same precision and point position as the inputs.
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
/// # use rcmp_simple::Dec;
/// let num = Dec::<2, 4>::new(true, [0, 0xFFFFFFFE]);
/// let sum = num + Dec::new(true, [0, 3]);
///
/// assert_eq!(sum, Dec::new(true, [1, 1]));
/// ```
///
/// # Notes
/// Note: `PRECISION` must always be `1` or greater. If `PRECISION == 0` then
/// this object will panic when various methods are called.
#[derive(Clone)]
pub struct Dec<const PRECISION: usize, const POINT: u32> {
    positive: bool,
    limbs: [u32; PRECISION],
}

impl<const PRECISION: usize, const POINT: u32> Dec<PRECISION, POINT> {
    /// Creates a new signed decimal with the given limbs.
    ///
    /// Numbers in the limbs are stored with the most significant limb first (at
    /// the smallest index) and the least significant limb last (at the largest
    /// index).
    pub fn new(positive: bool, limbs: [u32; PRECISION]) -> Dec<PRECISION, POINT> {
        Dec { positive, limbs }
    }

    /// Adds `self` and `rhs`, storing the sum into `into`, returning `true` if
    /// an overflow occured.
    ///
    /// # Examples
    /// ```rust
    /// # use rcmp_simple::Dec;
    /// let num = Dec::<2, 4>::new(true, [0xFFFFFFFF, 0xFFFFFFFE]);
    /// let mut sum = Default::default();
    /// let overflow = num.overflowing_add_into(&Dec::new(true, [0, 3]), &mut sum);
    ///
    /// assert_eq!(sum, Dec::new(true, [0, 1]));
    /// assert!(overflow);
    /// ```
    ///
    /// An example of adding a negative number to a positive one:
    /// ```rust
    /// # use rcmp_simple::Dec;
    /// let num = Dec::<2, 4>::new(true, [0x80000000, 0x00000000]);
    /// let mut sum = Default::default();
    /// let overflow = num.overflowing_add_into(&Dec::new(false, [0x20000000, 0x00000000]), &mut sum);
    ///
    /// assert_eq!(sum, Dec::new(true, [0x60000000, 0x00000000]));
    /// assert!(!overflow);
    /// ```
    pub fn overflowing_add_into(
        &self,
        rhs: &Dec<PRECISION, POINT>,
        into: &mut Dec<PRECISION, POINT>,
    ) -> bool {
        if self.positive == rhs.positive {
            add_n_into(&self.limbs, &rhs.limbs, &mut into.limbs)
        } else {
            // Figure out which of the numbers is largest so we can subtract the other from
            // it.
            let res = cmp(&self.limbs, &rhs.limbs);
            if res < 0 {
                // `rhs` is larger
                sub_n_into(&rhs.limbs, &self.limbs, &mut into.limbs);
                into.positive = !self.positive;
            } else if res > 0 {
                // `self` is larger
                sub_n_into(&self.limbs, &rhs.limbs, &mut into.limbs);
                into.positive = self.positive;
            } else {
                // `self` and `rhs` are equal
                zero(&mut into.limbs);
                into.positive = true;
            }

            // There should not be any overflow when subtracting
            false
        }
    }

    /// Adds `self` and `rhs`, storing the sum into `self, returning `true` if
    /// an overflow occurred.
    ///
    /// # Example
    /// ```rust
    /// # use rcmp_simple::Dec;
    /// let mut num = Dec::<2, 4>::new(true, [0xFFFFFFFF, 0xFFFFFFFE]);
    /// let overflow = num.overflowing_add_mut(&Dec::new(true, [0, 3]));
    ///
    /// assert_eq!(num, Dec::new(true, [0, 1]));
    /// assert!(overflow);
    /// ```
    pub fn overflowing_add_mut(&mut self, rhs: &Dec<PRECISION, POINT>) -> bool {
        if self.positive == rhs.positive {
            add_n_mut(&mut self.limbs, &rhs.limbs)
        } else {
            // Figure out which of the numbers is largest so we can subtract the other from
            // it.
            let res = cmp(&self.limbs, &rhs.limbs);
            if res < 0 {
                // `rhs` is larger
                sub_n_mut_2(&rhs.limbs, &mut self.limbs);
                self.positive = !self.positive;
            } else if res > 0 {
                // `self` is larger
                sub_n_mut(&mut self.limbs, &rhs.limbs);
            } else {
                // `self` and `rhs` are equal
                zero(&mut self.limbs);
                self.positive = true;
            }

            // There should not be any overflow when subtracting
            false
        }
    }

    /// Subtracts `rhs` from `self`, storing the difference into `into`,
    /// returning `true` if an overflow occurred.
    ///
    /// # Examples
    /// ```rust
    /// # use rcmp_simple::Dec;
    /// let num = Dec::<2, 4>::new(true, [1, 0]);
    /// let mut dif = Default::default();
    /// let overflow = num.overflowing_sub_into(&Dec::new(true, [0, 1]), &mut dif);
    ///
    /// assert_eq!(dif, Dec::new(true, [0, 0xFFFFFFFF]));
    /// assert!(!overflow);
    /// ```
    ///
    /// An example of subtracting a larger number from a smaller number:
    /// ```rust
    /// # use rcmp_simple::Dec;
    /// let num = Dec::<2, 4>::new(true, [0, 1]);
    /// let mut dif = Default::default();
    /// let overflow = num.overflowing_sub_into(&Dec::new(true, [0, 2]), &mut dif);
    ///
    /// assert_eq!(dif, Dec::new(false, [0, 1]));
    /// assert!(!overflow);
    /// ```
    pub fn overflowing_sub_into(
        &self,
        rhs: &Dec<PRECISION, POINT>,
        into: &mut Dec<PRECISION, POINT>,
    ) -> bool {
        if self.positive != rhs.positive {
            add_n_into(&self.limbs, &rhs.limbs, &mut into.limbs)
        } else {
            // Figure out which of the numbers is largest so we can subtract the other from
            // it.
            let res = cmp(&self.limbs, &rhs.limbs);
            if res < 0 {
                // `rhs` is larger
                sub_n_into(&rhs.limbs, &self.limbs, &mut into.limbs);
                into.positive = !self.positive;
            } else if res > 0 {
                // `self` is larger
                sub_n_into(&self.limbs, &rhs.limbs, &mut into.limbs);
                into.positive = self.positive;
            } else {
                // `self` and `rhs` are equal
                zero(&mut into.limbs);
                into.positive = true;
            }

            // There should not be any overflow when subtracting
            false
        }
    }

    /// Subtracts `rhs` from `self`, storing the difference into `self`,
    /// returning `true` if an overflow occurred.
    ///
    /// # Examples
    /// ```rust
    /// # use rcmp_simple::Dec;
    /// let mut num = Dec::<2, 4>::new(true, [0, 1]);
    /// let overflow = num.overflowing_sub_mut(&Dec::new(true, [0, 2]));
    ///
    /// assert_eq!(num, Dec::new(false, [0, 1]));
    /// assert!(!overflow);
    /// ```
    pub fn overflowing_sub_mut(&mut self, rhs: &Dec<PRECISION, POINT>) -> bool {
        if self.positive != rhs.positive {
            add_n_mut(&mut self.limbs, &rhs.limbs)
        } else {
            // Figure out which of the numbers is largest so we can subtract the other from
            // it.
            let res = cmp(&self.limbs, &rhs.limbs);
            if res < 0 {
                // `rhs` is larger
                sub_n_mut_2(&rhs.limbs, &mut self.limbs);
                self.positive = !self.positive;
            } else if res > 0 {
                // `self` is larger
                sub_n_mut(&mut self.limbs, &rhs.limbs);
            } else {
                // `self` and `rhs` are equal
                zero(&mut self.limbs);
                self.positive = true;
            }

            // There should not be any overflow when subtracting
            false
        }
    }

    /// Multiplies `rhs` by `self`, storing the lower half of the result into
    /// `into`, returning true if the upper half of the result would be
    /// non-zero.
    ///
    /// # Examples
    /// ```rust
    /// # use rcmp_simple::Dec;
    /// //   0x4.0000004,00000000
    /// let num = Dec::<2, 4>::new(true, [0x40000004, 0x00000000]);
    /// let mut prod = Default::default();
    ///
    /// // * 0x2.0000002,00000000
    /// let overflow = num.overflowing_mul_into(&Dec::new(true, [0x20000002, 0x00000000]), &mut prod);
    ///
    /// // = 0x8.0000010,00000080
    /// assert_eq!(prod, Dec::new(true, [0x80000010, 0x00000080]));
    /// assert!(!overflow);
    /// ```
    ///
    /// An example of multiplying a positive number by a negative number:
    /// ```rust
    /// # use rcmp_simple::Dec;
    /// let num = Dec::<2, 4>::new(true, [0x40000000, 0]);
    /// let mut prod = Default::default();
    /// let overflow = num.overflowing_mul_into(&Dec::new(false, [0x20000000, 0]), &mut prod);
    ///
    /// assert_eq!(prod, Dec::new(false, [0x80000000, 0]));
    /// assert!(!overflow);
    /// ```
    pub fn overflowing_mul_into(
        &self,
        rhs: &Dec<PRECISION, POINT>,
        into: &mut Dec<PRECISION, POINT>,
    ) -> bool
    where
        [(); PRECISION * 2]:,
    {
        // Determine the sign of `into`
        into.positive = self.positive == rhs.positive;

        // Create temporary storage for intermediate (non-bit-shifted, double-PRECISION)
        // results of multiplication.
        let mut temp = [0u32; PRECISION * 2];

        // Perform the multilication.
        for j in (0..PRECISION).rev() {
            let b = rhs.limbs[j];

            // Here, we're multiplying everything by `b` so if `b == 0` then nothing is
            // happening, so let's just skip it entirely.
            if b != 0 {
                // Add each iteration to the `into` array. Note that this will never overflow.
                // The fact that results are being added here is what allows
                // this to carry between iterations of the `j` loop.
                let carry = addmul_1_full(&self.limbs, b, &mut temp, j + 1);

                // Note that `j` never increases, so `temp[j]` will always be zero before we
                // set it here, meaning that no addition is necessary.
                temp[j] = carry;
            }
        }

        // Calculate the bitshift and wordshift
        let bitshift = POINT & 0x1F;
        let wordshift = (POINT >> 5) as usize;

        // Perform a bit-shifted copy into the `into` structure, discarding anything
        // outside our precision and keeping track of anything overflowing our
        // precision.
        for i in (0..PRECISION).rev() {
            let h = i + wordshift;

            if bitshift == 0 {
                into.limbs[i] = temp[h];
            } else {
                into.limbs[i] = (temp[h] << bitshift) | (temp[h + 1] >> (32 - bitshift));
            }
        }

        // Note that overflow calculation is separate and may be omitted if not needed.
        let mut overflow = false;

        // Check whether each of the remaining words is zero.
        for i in (0..wordshift).rev() {
            if bitshift == 0 {
                overflow |= temp[i] != 0;
            } else {
                overflow |= (temp[i] << bitshift) | (temp[i + 1] >> (32 - bitshift)) != 0;
            }
        }

        // Check whether the remaining bits are zero.
        if bitshift != 0 {
            overflow |= temp[0] >> (32 - bitshift) != 0;
        }

        overflow
    }
}

impl<const PRECISION: usize, const POINT: u32> PartialEq for Dec<PRECISION, POINT> {
    fn eq(&self, other: &Self) -> bool {
        // custom `PartialEq` implementation that considers `+0 == -0`
        let mut is_zero = true;

        for i in 0..PRECISION {
            let a = self.limbs[i];
            if a != other.limbs[i] {
                return false;
            }
            if a != 0 {
                is_zero = false;
            }
        }

        if is_zero {
            true
        } else {
            self.positive == other.positive
        }
    }
}

impl<const PRECISION: usize, const POINT: u32> Default for Dec<PRECISION, POINT> {
    fn default() -> Self {
        Dec::new(true, [0; PRECISION])
    }
}

impl<const PRECISION: usize, const POINT: u32> Debug for Dec<PRECISION, POINT> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}UDec<{}, {}>[{}]",
            if self.positive { "-" } else { "" },
            PRECISION,
            POINT,
            self.limbs
                .iter()
                .format_with(", ", |e, f| f(&format_args!("0x{:08X}", e)))
        )
    }
}

impl<const PRECISION: usize, const POINT: u32> Add for Dec<PRECISION, POINT> {
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

impl<const PRECISION: usize, const POINT: u32> Sub for Dec<PRECISION, POINT> {
    type Output = Self;

    /// Performs the `-` operation.
    ///
    /// # Panics
    /// This function panics if an overflow occurs and debug assertions are
    /// enabled. Otherwise, this function will wrap.
    fn sub(self, rhs: Self) -> Self::Output {
        let mut res = Default::default();
        let overflow = self.overflowing_sub_into(&rhs, &mut res);
        debug_assert!(!overflow, "Subtract overflowed");
        res
    }
}

impl<const PRECISION: usize, const POINT: u32> Mul for Dec<PRECISION, POINT>
where
    [(); PRECISION * 2]:,
{
    type Output = Self;

    /// Performs the `*` operation.
    ///
    /// # Panics
    /// This function panics if an overflow occurs and debug assertions are
    /// enabled. Otherwise, this function will wrap.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut res = Default::default();
        let overflow = self.overflowing_mul_into(&rhs, &mut res);
        debug_assert!(!overflow, "Multiply overflowed");
        res
    }
}

impl<const PRECISION: usize, const POINT: u32> AddAssign for Dec<PRECISION, POINT> {
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

impl<const PRECISION: usize, const POINT: u32> SubAssign for Dec<PRECISION, POINT> {
    /// Performs the `-=` operation.
    ///
    /// # Panics
    /// This function panics if an overflow occurs and debug assertions are
    /// enabled. Otherwise this function will wrap.
    fn sub_assign(&mut self, rhs: Self) {
        let overflow = self.overflowing_sub_mut(&rhs);
        debug_assert!(!overflow, "Subtract overflowed");
    }
}

impl<const PRECISION: usize, const POINT: u32> MulAssign for Dec<PRECISION, POINT>
where
    [(); PRECISION * 2]:,
{
    /// Performs the `*=` operation.
    ///
    /// # Panics
    /// This function panics if an overflow occurs and debug assertions are
    /// enabled. Otherwise this function will wrap.
    fn mul_assign(&mut self, rhs: Self) {
        let mut res = Default::default();
        let overflow = self.overflowing_mul_into(&rhs, &mut res);
        debug_assert!(!overflow, "Multiply overflowed");
        *self = res;
    }
}

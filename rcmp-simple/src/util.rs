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

/// This function multiplies two `u32`s together to get the high and low 32-bit
/// words of the 64-bit result.
///
/// # Returns
/// This returns `u32` in the order (`high`, `low`).
pub fn mul_hi_low(a: u32, b: u32) -> (u32, u32) {
    // We perform this multiplication without using `u64`s by breaking each `u32` up
    // into two 16-bit pieces and multiplying those.

    let al = a & 0xFFFF;
    let ah = (a >> 0x10) & 0xFFFF;
    let bl = b & 0xFFFF;
    let bh = (b >> 0x10) & 0xFFFF;

    let mid1 = ah * bl;
    let mid2 = al * bh;

    let mut carry = 0u32;
    let low = al * bl;
    let low2 = low.wrapping_add((mid1 & 0xFFFF) << 0x10);
    carry += (low2 < low) as u32;
    let low3 = low2.wrapping_add((mid2 & 0xFFFF) << 0x10);
    carry += (low3 < low2) as u32;
    let high = ah * bh + ((mid1 >> 0x10) & 0xFFFF) + ((mid2 >> 0x10) & 0xFFFF) + carry;

    (high, low3)
}

#[cfg(test)]
mod test {
    use crate::util::mul_hi_low;

    #[test]
    fn test_mul_hi_low() {
        let (high, low) = mul_hi_low(0xFFFFFFFF, 0xFFFFFFFF);

        assert_eq!(low, 0x00000001, "Low should be 0x00000001");
        assert_eq!(high, 0xFFFFFFFE, "High should be 0xFFFFFFFE");
    }
}

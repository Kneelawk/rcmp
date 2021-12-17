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

/// Natural number extended fixed precision implementation. This only holds
/// positive integers or 0. This struct is generic over precision. All
/// operations are precision-consistent, returning natural numbers with the same
/// precision as that of the inputs.
pub struct NaturalNumber<const PRECISION: usize> {
    /// Numbers are stored with the most significant limb first (at the smallest
    /// index) and the least significant limb last (at the largest index).
    limbs: [u32; PRECISION],
}

impl<const PRECISION: usize> NaturalNumber<PRECISION> {
    /// Adds `self` and `rhs` returning a new natural number that is the sum of
    /// these two numbers.
    pub fn overflowing_add(
        &self,
        rhs: &NaturalNumber<PRECISION>,
    ) -> (NaturalNumber<PRECISION>, bool) {
        let mut limbs = [0u32; PRECISION];
        let mut carry = false;

        for i in (0..PRECISION).rev() {
            limbs[i] = self.limbs[i]
                .wrapping_add(rhs.limbs[i])
                .wrapping_add(if carry { 1 } else { 0 });
            carry = limbs[i] < self.limbs[i];
        }

        (NaturalNumber { limbs }, carry)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}

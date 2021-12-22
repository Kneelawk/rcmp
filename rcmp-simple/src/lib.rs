// rcmp-simple - A simple concept implementation of multiprecision.
//
// Copyright (C) 2021  Jed Pommert (Kneelawk)
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

// Using complicated featurs like this one is ok because we can emulate similar
// things in the WGSL implementation using macros.
#![feature(generic_const_exprs)]

//! # About
//! This library is a simple concept implementation of multiprecision algorithms
//! in rust. The name RCMP stands for Rust Concept Multi-Precision. This library
//! is called a multiprecision library, however, the intended use of this
//! library is actually just to provide expanded, fixed precision types. A more
//! apt name for this library might be Rust Concept Fixed-Precision, however
//! this creates the acronym RCFP which could easily be confused with Rust
//! Concept Floating Point.
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
//! # Types
//! This library provides these types for performing fixed-precision arithmetic:
//! * [`UInt`] - This type is an unsigned integer type with
//!   compile-time-arbitrary fixed-precision.
//! * [`UDec`] - This type is an unsigned decimal type with
//!   compile-time-arbitrary fixed-precision and fixed-point.
//! * [`Dec`] - This type is a signed decimal type with compile-time-arbitrary
//!   fixed-precision and fixed-point. This type is the goal for WGSL
//!   implementation and the endpoint for Rust implementation.
//!
//! # Examples
//! Each type implements basic arithmetic operations such as addition,
//! subtraction, multiplication, and division. The goal is also for the [`Dec`]
//! type to implement more complicated operations such as squaring,
//! exponentiation (e<sup>x</sup>), and trigonometric functions.
//!
//! An example of simple arithmetic using the [`UInt`] type:
//! ```rust
//! # use rcmp_simple::UInt;
//! let num = UInt::new([0, 0xFFFFFFFE]);
//! let sum = num + UInt::new([0, 5]);
//!
//! assert_eq!(sum, UInt::new([1, 3]));
//! ```

mod dec;
mod udec;
mod uint;
mod util;

pub use dec::Dec;
pub use udec::UDec;
pub use uint::UInt;

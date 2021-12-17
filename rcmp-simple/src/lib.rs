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

mod uint;

pub use uint::UnsignedInteger;

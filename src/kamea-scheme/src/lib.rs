//! # kamea-scheme
//!
//! R4RS Scheme grounded in a 64×64 Cayley table (4KB).
//!
//! Type dispatch, small-value arithmetic, and type predicates are
//! algebraic operations — single table lookups with no branching.
//!
//! `no_std` compatible. Zero dependencies.
//!
//! ```
//! use kamea_scheme::table;
//!
//! // Fixnum addition via the Cayley table: 3 + 5 = 8
//! let result = table::dot(table::fixnum(3), table::fixnum(5));
//! assert_eq!(result, table::fixnum(8));
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

pub mod table;
pub mod value;
pub mod heap;

// Re-exports
pub use value::Val;
pub use table::dot;

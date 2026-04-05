//! # wispy-scheme
//!
//! R4RS Scheme in 1KB. Rib-based values, table-driven type dispatch, `no_std`.
//!
//! Named after Wispy the guinea pig.
//!
//! ```
//! use wispy_scheme::table;
//!
//! // Type dispatch via the Cayley table
//! assert_eq!(table::dot(table::CAR, table::T_PAIR), table::T_PAIR); // car of pair → valid
//! assert_eq!(table::dot(table::CAR, table::T_STR), table::BOT);     // car of string → error
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(all(feature = "alloc", not(feature = "std")))]
extern crate alloc;

pub mod table;
pub mod val;
pub mod heap;
pub mod symbol;
pub mod reader;
#[cfg(feature = "std")]
pub mod macros;
#[cfg(feature = "std")]
pub mod eval;
#[cfg(feature = "std")]
pub mod cps;
#[cfg(feature = "std")]
pub mod compile;

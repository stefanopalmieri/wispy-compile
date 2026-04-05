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

pub mod table;
pub mod val;
pub mod heap;
pub mod symbol;
pub mod reader;
pub mod eval;
pub mod cps;
pub mod compile;

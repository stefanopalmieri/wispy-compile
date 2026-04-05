//! # kamea-scheme
//!
//! R4RS Scheme in 1KB. Rib-based values, table-driven type dispatch, `no_std`.
//!
//! ```
//! use kamea_scheme::table;
//!
//! // Type dispatch via the Cayley table
//! assert_eq!(table::dot(table::CAR, table::T_PAIR), table::T_PAIR); // car of pair → valid
//! assert_eq!(table::dot(table::CAR, table::T_STR), table::BOT);     // car of string → error
//! assert_eq!(table::dot(table::TAU, table::T_SYM), table::T_SYM);   // τ(symbol) → symbol tag
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

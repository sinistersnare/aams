//! Flat Abstract Machine:
//! This machine is an abstract CESK* for a subset of the
//! Scheme programming language.
//!
//! It features flat-closures, as opposed to the standard linked-closure.
//! This method is derived from Might et al.'s 2010 paper on the m-CFA algorithm.
//!
//! This is an Abstracted Abstract Machine, based off of the
//! DVH paper of a similar name (see readme).
//!
//! Using this method, we have a polynomial CFA algorithm!
//!
//! I also use the continuation-allocator from Pushdown For Free by Gilray et al.
//! This allows perfect stack precision for our continuation allocation.


mod domains;
mod evaluate;
mod prims;

pub use evaluate::evaluate;

pub const M: usize = 2;

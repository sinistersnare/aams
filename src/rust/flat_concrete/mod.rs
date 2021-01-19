//! Flat Concrete Machine:
//! This machine is a CESK* for a subset of the Scheme programming language.
//! It features flat-closures, as opposed to the standard linked-closure.
//! This method is derived from Might et al.'s 2010 paper on the m-CFA algorithm.

mod domains;
mod evaluate;
mod prims;

pub use evaluate::evaluate;

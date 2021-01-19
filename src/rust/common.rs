//! Domains and other types that should be common in all machines
//! This makes some things _very_ easy to transfer from concrete to abstract.
//! The domains.rs files of the machines are machine-dependent domains.

use std::fmt;

#[derive(Hash, Clone, PartialEq, Eq)]
pub enum Expr {
   List(Vec<Expr>),
   Atom(String),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Var(pub String);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Prim(pub String);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum LambdaArgType {
   FixedArg(Vec<Var>),
   VarArg(Var),
}

impl fmt::Debug for Expr {
   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      match self {
         Expr::List(ref list) => {
            write!(f, "(")?;
            for (i, e) in list.iter().enumerate() {
               write!(f, "{:?}", e)?;
               if i + 1 != list.len() {
                  write!(f, " ")?;
               }
            }
            write!(f, ")")
         }
         Expr::Atom(ref atom) => write!(f, "{}", atom),
      }
   }
}

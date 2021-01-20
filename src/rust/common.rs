//! Domains and other types that should be common in all machines
//! This makes some things _very_ easy to transfer from concrete to abstract.
//! The domains.rs files of the machines are machine-dependent domains.

use crate::matching::{match_syntax, Matching};
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

pub fn find_frees(expr: Expr, bound: im::HashSet<Var>) -> im::Vector<Var> {
   match match_syntax(expr) {
      Matching::If(ec, et, ef) => {
         let ec_free = find_frees(ec, bound.clone());
         let et_free = find_frees(et, bound.clone());
         let ef_free = find_frees(ef, bound);
         ec_free + et_free + ef_free
      }
      Matching::Let(vars, exprs, eb) => {
         let bindings_free: im::Vector<Var> = exprs
            .into_iter()
            .map(|expr| find_frees(expr, bound.clone()))
            .flatten()
            .collect();
         bindings_free + find_frees(eb, bound + vars.into_iter().collect())
      }
      Matching::SetBang(var, expr) => {
         let var_free = if bound.contains(&var) {
            im::Vector::new()
         } else {
            im::Vector::unit(var)
         };
         var_free + find_frees(expr, bound)
      }
      Matching::Callcc(expr) => find_frees(expr, bound),
      Matching::Apply(ef, ea) => find_frees(ef, bound.clone()) + find_frees(ea, bound),
      Matching::Call(args) => args
         .into_iter()
         .map(|expr| find_frees(expr, bound.clone()))
         .flatten()
         .collect(),
      Matching::Lambda(argtype, body) => match argtype {
         LambdaArgType::FixedArg(args) => find_frees(body, bound + args.into_iter().collect()),
         LambdaArgType::VarArg(arg) => find_frees(body, bound.update(arg)),
      },
      Matching::StrAtom(a) => {
         let var = Var(a);
         if bound.contains(&var) {
            im::Vector::new()
         } else {
            im::Vector::unit(var)
         }
      }
      Matching::Quote(..) | Matching::Number(..) | Matching::Boolean(..) => im::Vector::new(),
   }
}

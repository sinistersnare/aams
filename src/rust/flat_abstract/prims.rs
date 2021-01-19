use std::collections::HashMap;

use crate::common::Prim;
use crate::flat_abstract::domains::{InnerVal, Val};

fn prim_add(args: &[Val]) -> Val {
   Val::from(InnerVal::Number(69))
}

fn prim_mult(args: &[Val]) -> Val {
   Val::from(InnerVal::Number(69))
}

fn prim_cons(args: &[Val]) -> Val {
   Val::from(InnerVal::Number(69))
}

fn prim_car(args: &[Val]) -> Val {
   Val::from(InnerVal::Number(69))
}

fn prim_cdr(args: &[Val]) -> Val {
   Val::from(InnerVal::Number(69))
}

fn prim_null(_: &[Val]) -> Val {
   Val::from(InnerVal::Null)
}

type PrimFunc = fn(&[Val]) -> Val;

lazy_static! {
   pub static ref PRIMS: HashMap<&'static str, PrimFunc> = {
      let mut m = HashMap::new();
      m.insert("+", prim_add as PrimFunc);
      m.insert("*", prim_mult as PrimFunc);
      m.insert("cons", prim_cons as PrimFunc);
      m.insert("car", prim_car as PrimFunc);
      m.insert("cdr", prim_cdr as PrimFunc);
      m.insert("null", prim_null as PrimFunc);
      m
   };
}

pub fn apply_prim(Prim(op): Prim, args: &[Val]) -> Val {
   (*PRIMS.get::<str>(&op).expect("Prim doesnt exist!"))(args)
}

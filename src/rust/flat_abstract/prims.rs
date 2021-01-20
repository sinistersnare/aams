use std::collections::HashMap;

use crate::common::Prim;
use crate::flat_abstract::domains::{InnerVal, Val};

fn prim_add(args: &[Val]) -> Val {
   let mut ret = 0;
   for v in args {
      if let Some(n) = v.is_number() {
         ret += n;
      } else {
         return Val::top();
      }
   }
   Val::from(InnerVal::Number(ret))
}

fn prim_mult(args: &[Val]) -> Val {
   let mut ret = 1;
   for v in args {
      if let Some(n) = v.is_number() {
         ret *= n;
      } else {
         return Val::top();
      }
   }
   Val::from(InnerVal::Number(ret))
}

fn prim_cons(args: &[Val]) -> Val {
   if args.len() != 2 {
      panic!("cons Error. Expected 2 args, given {:?}", args);
   }
   let (car, cdr) = (args[0].clone(), args[1].clone());
   Val::from(InnerVal::Cons(Box::new(car), Box::new(cdr)))
}

fn prim_car(args: &[Val]) -> Val {
   if args.len() != 1 {
      panic!("car Error. Expected 1 arg, given {:?}", args);
   }
   if let Some((car, _cdr)) = args[0].is_cons() {
      *car
   } else {
      Val::top()
   }
}

fn prim_cdr(args: &[Val]) -> Val {
   if args.len() != 1 {
      panic!("car Error. Expected 1 arg, given {:?}", args);
   }
   if let Some((_car, cdr)) = args[0].is_cons() {
      *cdr
   } else {
      Val::top()
   }
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

use std::collections::HashMap;

use crate::common::Prim;
use crate::flat_concrete::domains::Val;

fn prim_add(args: &[Val]) -> Val {
   let mut ret = 0;
   for v in args {
      match v {
         Val::Number(n) => {
            ret += n;
         }
         other => {
            panic!("+ Type error. Expect number, got {:?}", other);
         }
      }
   }
   Val::Number(ret)
}

fn prim_mult(args: &[Val]) -> Val {
   let mut ret = 1;
   for v in args {
      match v {
         Val::Number(n) => {
            ret *= n;
         }
         other => {
            panic!("* Type error. Expect number, got {:?}", other);
         }
      }
   }
   Val::Number(ret)
}

fn prim_cons(args: &[Val]) -> Val {
   if args.len() != 2 {
      panic!("cons Error. Expected 2 args, given {:?}", args);
   }
   let (car, cdr) = (args[0].clone(), args[1].clone());
   Val::Cons(Box::new(car), Box::new(cdr))
}

fn prim_car(args: &[Val]) -> Val {
   if args.len() != 1 {
      panic!("car Error. Expected 1 arg, given {:?}", args);
   }
   match &args[0] {
      Val::Cons(car, _) => *car.clone(),
      other => {
         panic!("car Type error. Expect number, got {:?}", other);
      }
   }
}

fn prim_cdr(args: &[Val]) -> Val {
   if args.len() != 1 {
      panic!("cdr Error. Expected 1 arg, given {:?}", args);
   }
   match &args[0] {
      Val::Cons(_, cdr) => *cdr.clone(),
      other => {
         panic!("cdr Type error. Expect number, got {:?}", other);
      }
   }
}

fn prim_null(_: &[Val]) -> Val {
   Val::Null
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

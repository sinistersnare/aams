use std::collections::HashMap;

use crate::common::{Prim, Val};

fn prim_add(args: &[Val]) -> Val {
   let mut ret = 0;
   for arg in args {
      if let Val::Number(n) = arg {
         ret += n;
      } else {
         panic!("Not given a number to add!");
      }
   }
   Val::Number(ret)
}

fn prim_mult(args: &[Val]) -> Val {
   let mut ret = 1;
   for arg in args {
      if let Val::Number(n) = arg {
         ret *= n;
      } else {
         panic!("Not given a number to multiply!");
      }
   }
   Val::Number(ret)
}

fn prim_cons(args: &[Val]) -> Val {
   if args.len() != 2 {
      panic!("Cons takes 2 arguments, given {}", args.len());
   }
   let (car, cdr) = (args[0].clone(), args[1].clone());
   Val::Cons(Box::new(car), Box::new(cdr))
}

fn prim_car(args: &[Val]) -> Val {
   if args.len() != 1 {
      panic!("Car takes 1 argument, given {}", args.len());
   }
   match args[0] {
      Val::Cons(ref car, _) => *car.clone(),
      _ => panic!("Not given a Cons."),
   }
}

fn prim_cdr(args: &[Val]) -> Val {
   if args.len() != 1 {
      panic!("Cdr takes 1 argument, given {}", args.len());
   }
   match args[0] {
      Val::Cons(_, ref cdr) => *cdr.clone(),
      _ => panic!("Not given a Cons."),
   }
}

fn prim_null(args: &[Val]) -> Val {
   if !args.is_empty() {
      panic!("Null takes 0 arguments, Given {}", args.len());
   }
   Val::Null
}

lazy_static! {
   pub static ref PRIMS: HashMap<&'static str, fn(&[Val]) -> Val> = {
      let mut m = HashMap::new();
      m.insert("+", prim_add as fn(&[Val]) -> Val);
      m.insert("*", prim_mult as fn(&[Val]) -> Val);
      m.insert("cons", prim_cons as fn(&[Val]) -> Val);
      m.insert("car", prim_car as fn(&[Val]) -> Val);
      m.insert("cdr", prim_cdr as fn(&[Val]) -> Val);
      m.insert("null", prim_null as fn(&[Val]) -> Val);
      m
   };
}

pub fn apply_prim(Prim(op): Prim, args: &[Val]) -> Val {
   (*PRIMS.get::<str>(&op).expect("Prim doesnt exist!"))(args)
}

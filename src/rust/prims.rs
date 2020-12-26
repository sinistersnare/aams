use std::collections::HashMap;

use crate::common::{ConcreteVal, Prim, Val};

fn prim_add(args: &Val) -> Val {
   let mut ret = 0;
   let mut cur = args;
   loop {
      match cur.vals {
         Err(_) => return Val::top(), // idfk
         Ok(ConcreteVal::Cons(ref car, _)) => match car.vals {
            Err(true) => return Val::top(),
            Ok(ConcreteVal::Number(n)) => {
               ret += n;
            }
            _ => {
               panic!("Not given a number to add!");
            }
         },
         Ok(ref other) => {
            panic!("Not given list, given {:?}", other);
         }
      }
      cur = match cur.vals {
         Err(_) => unreachable!(),
         Ok(ConcreteVal::Cons(_, ref cdr)) => &*cdr,
         Ok(ConcreteVal::Null) => {
            break;
         }
         Ok(_) => unreachable!(),
      }
   }

   Val::new(ConcreteVal::Number(ret))
}

fn prim_mult(args: &Val) -> Val {
   let mut ret = 1;
   let mut cur = args;
   loop {
      match cur.vals {
         Err(_) => return Val::top(), // idfk
         Ok(ConcreteVal::Cons(ref car, _)) => match car.vals {
            Err(true) => return Val::top(),
            Ok(ConcreteVal::Number(n)) => {
               ret *= n;
            }
            _ => {
               panic!("Not given a number to add!");
            }
         },
         Ok(ref other) => {
            panic!("Not given list, given {:?}", other);
         }
      }
      cur = match cur.vals {
         Err(_) => unreachable!(),
         Ok(ConcreteVal::Cons(_, ref cdr)) => &*cdr,
         Ok(ConcreteVal::Null) => {
            break;
         }
         Ok(_) => unreachable!(),
      }
   }

   Val::new(ConcreteVal::Number(ret))
}

fn prim_cons(args: &Val) -> Val {
   match args.vals {
      Err(true) => Val::top(),
      Ok(ConcreteVal::Cons(ref car, ref cdr)) => match cdr.vals {
         Err(true) => Val::top(),
         Ok(ConcreteVal::Cons(ref cadr, ref cddr)) => match cddr.vals {
            Err(true) => Val::top(),
            Ok(ConcreteVal::Null) => Val::new(ConcreteVal::Cons(car.clone(), cadr.clone())),
            ref other => {
               panic!("Bad args to cons (3rd level) {:?}", other);
            }
         },
         ref other => {
            panic!("Bad args to cons (2nd level) {:?}", other);
         }
      },
      ref other => {
         panic!("Bad args to cons: {:?}", other);
      }
   }
}

fn prim_car(args: &Val) -> Val {
   match args.vals {
      Err(true) => Val::top(),
      Ok(ConcreteVal::Cons(ref arg1, ref rest)) => match rest.vals {
         Err(true) => Val::top(),
         Ok(ConcreteVal::Null) => match arg1.vals {
            Err(true) => Val::top(),
            Ok(ConcreteVal::Cons(ref car, _)) => *car.clone(),
            ref other => {
               panic!("`car` not given a cons: {:?}", other);
            }
         },
         ref other => {
            panic!("Bad args to car (2nd level): {:?}", other);
         }
      },
      ref other => {
         panic!("Bad args to car: {:?}", other);
      }
   }
}

fn prim_cdr(args: &Val) -> Val {
   match args.vals {
      Err(true) => Val::top(),
      Ok(ConcreteVal::Cons(ref arg1, ref rest)) => match rest.vals {
         Err(true) => Val::top(),
         Ok(ConcreteVal::Null) => match arg1.vals {
            Err(true) => Val::top(),
            Ok(ConcreteVal::Cons(_, ref cdr)) => *cdr.clone(),
            ref other => {
               panic!("`car` not given a cons: {:?}", other);
            }
         },
         ref other => {
            panic!("Bad args to car: {:?}", other);
         }
      },
      ref other => {
         panic!("Bad args to car: {:?}", other);
      }
   }
}

fn prim_null(_: &Val) -> Val {
   Val::new(ConcreteVal::Null)
}

lazy_static! {
   pub static ref PRIMS: HashMap<&'static str, fn(&Val) -> Val> = {
      let mut m = HashMap::new();
      m.insert("+", prim_add as fn(&Val) -> Val);
      m.insert("*", prim_mult as fn(&Val) -> Val);
      m.insert("cons", prim_cons as fn(&Val) -> Val);
      m.insert("car", prim_car as fn(&Val) -> Val);
      m.insert("cdr", prim_cdr as fn(&Val) -> Val);
      m.insert("null", prim_null as fn(&Val) -> Val);
      m
   };
}

pub fn apply_prim(Prim(op): Prim, args: &Val) -> Val {
   (*PRIMS.get::<str>(&op).expect("Prim doesnt exist!"))(args)
}

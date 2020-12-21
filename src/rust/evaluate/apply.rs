//!
//! Items to do with 'apply states'.
//! Apply states are evaluating the current-continuation
//! because the control is a value.

use crate::common::{
   apply_alloc, apply_state, eval_state, make_scm_list, scm_list_to_vals, val_is_list, ApplyState,
   CloType, Closure, Expr, Kont, State, Val,
};
use crate::prims::apply_prim;

fn handle_if_kont(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::If(et, ef, ifenv, next_kaddr) = k {
      let next_e = if val == Val::Boolean(false) { ef } else { et };
      eval_state(next_e, ifenv, store, next_kaddr)
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_let_kont(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::Let(vars, mut done, mut todo, eb, letenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let mut next_env = letenv;
         let mut next_store = store;
         for (i, (bndvar, val)) in vars.iter().zip(done.iter()).enumerate() {
            let addr = apply_alloc(st, i);
            next_env = next_env.insert(bndvar.clone(), addr.clone());
            next_store = next_store.insert(addr, val.clone());
         }
         eval_state(eb, next_env, next_store, next_kaddr)
      } else {
         let head = todo.remove(0);
         let next_next_kaddr = apply_alloc(st, 0);
         let next_k = Kont::Let(vars, done, todo, eb, letenv.clone(), next_kaddr);
         let next_store = store.insertk(next_next_kaddr.clone(), next_k);
         eval_state(head, letenv, next_store, next_next_kaddr)
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_prim_kont(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::Prim(op, mut done, mut todo, primenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let val = apply_prim(op, &done);
         apply_state(val, store, next_kaddr)
      } else {
         let head = todo.remove(0);
         let next_next_kaddr = apply_alloc(st, 0);
         let next_k = Kont::Prim(op, done, todo, primenv.clone(), next_kaddr);
         let next_store = store.insertk(next_next_kaddr.clone(), next_k);
         eval_state(head, primenv, next_store, next_next_kaddr)
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_apply_prim_kont(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::ApplyPrim(op, next_kaddr) = k {
      if !val_is_list(&val) {
         panic!("Apply not given a list.");
      }
      let val = apply_prim(op, &scm_list_to_vals(val));
      apply_state(val, store, next_kaddr)
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_callcc_kont(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::Callcc(ref next_kaddr) = k {
      if let Val::Closure(Closure(clotype, body, cloenv)) = val {
         match clotype {
            CloType::MultiArg(mut params) => {
               if params.len() != 1 {
                  panic!("call/cc lambda only takes 1 argument!");
               }
               let addr = apply_alloc(st, 0);
               let next_k = match store.get(next_kaddr) {
                  Some(Val::Kont(k)) => k,
                  Some(other) => panic!("Not given a K: {:?}", other),
                  None => panic!("K not found with addr: {:?}", next_kaddr),
               };
               let next_env = cloenv.insert(params.remove(0), addr.clone());
               let next_store = store.insert(addr, Val::Kont(next_k));
               eval_state(body, next_env, next_store, next_kaddr.clone())
            }
            CloType::VarArg(_) => {
               panic!("call/cc takes a multi-arg lambda, not vararg");
            }
         }
      } else if let Val::Kont(kv) = val {
         let next_kaddr = apply_alloc(st, 0);
         let next_store = store.insertk(next_kaddr.clone(), kv);
         apply_state(Val::Kont(k.clone()), next_store, next_kaddr)
      } else {
         panic!("Call/cc given wrong type of argument.");
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_set_bang_kont(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::Set(addr, next_kaddr) = k {
      let next_store = store.insert(addr, val);
      apply_state(Val::Void, next_store, next_kaddr)
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_apply_list_kont(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::ApplyList(maybe_func, arglist, applyenv, next_kaddr) = k {
      match maybe_func {
         Some(func) => {
            if !val_is_list(&val) {
               panic!("Apply not given a list.");
            }
            if let Val::Closure(Closure(CloType::MultiArg(args), body, cloenv)) = *func {
               // this part turns the scheme-value into a rust-list
               // so that we can bind each value easier
               // not strictly necessary, but cleans up the next bit.
               let mut cur = val;
               let mut argvals = Vec::with_capacity(args.len());
               while !matches!(cur, Val::Null) {
                  if let Val::Cons(car, cdr) = cur {
                     argvals.push(*car);
                     cur = *cdr;
                  } else {
                     panic!("Not given a proper list somehow.");
                  }
               }
               if argvals.len() != args.len() {
                  panic!("Mismatch arg count between func and arglist.");
               }

               let mut next_env = cloenv;
               let mut next_store = store;
               for (i, (arg, argval)) in args.iter().zip(argvals.iter()).enumerate() {
                  let addr = apply_alloc(st, i);
                  next_env = next_env.insert(arg.clone(), addr.clone());
                  next_store = next_store.insert(addr, argval.clone());
               }
               eval_state(body, next_env, next_store, next_kaddr)
            } else if let Val::Closure(Closure(CloType::VarArg(arg), body, cloenv)) = *func {
               let addr = apply_alloc(st, 0);
               let next_env = cloenv.insert(arg, addr.clone());
               let next_store = store.insert(addr, val);
               eval_state(body, next_env, next_store, next_kaddr)
            } else {
               panic!("Not given a function in `(apply func arglist)`");
            }
         }
         None => {
            let next_next_kaddr = apply_alloc(st, 0);
            let next_k = Kont::ApplyList(
               Some(Box::new(val)),
               Expr::Atom("".into()),
               applyenv.clone(),
               next_kaddr,
            );
            let next_store = store.insertk(next_next_kaddr.clone(), next_k);
            eval_state(arglist, applyenv, next_store, next_next_kaddr)
         }
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_app(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::App(mut done, mut todo, appenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let head = done.remove(0);
         let mut args = done;
         if let Val::Closure(Closure(clotype, body, cloenv)) = head {
            match clotype {
               CloType::MultiArg(params) => {
                  if params.len() != args.len() {
                     panic!("arg # mismatch.");
                  }
                  let mut next_env = cloenv;
                  let mut next_store = store;
                  for (i, (param, arg)) in params.iter().zip(args.iter()).enumerate() {
                     let addr = apply_alloc(st, i);
                     next_env = next_env.insert(param.clone(), addr.clone());
                     next_store = next_store.insert(addr, arg.clone());
                  }
                  eval_state(body, next_env, next_store, next_kaddr)
               }
               CloType::VarArg(vararg) => {
                  let scm_list = make_scm_list(args);
                  let addr = apply_alloc(st, 0);
                  let next_env = cloenv.insert(vararg, addr.clone());
                  let next_store = store.insert(addr, scm_list);
                  eval_state(body, next_env, next_store, next_kaddr)
               }
            }
         } else if let Val::Kont(kv) = head {
            if args.len() != 1 {
               panic!("applying a kont only takes 1 argument.");
            }
            // replace the current continuation with the stored one.
            let next_next_kaddr = apply_alloc(st, 0);
            let next_store = store.insertk(next_next_kaddr.clone(), kv);
            apply_state(args.remove(0), next_store, next_next_kaddr)
         } else {
            panic!("Closure wasnt head of application");
         }
      } else {
         let head = todo.remove(0);
         let next_next_kaddr = apply_alloc(st, 0);
         let next_kont = Kont::App(done, todo, appenv.clone(), next_kaddr);
         let next_store = store.insertk(next_next_kaddr.clone(), next_kont);
         eval_state(head, appenv, next_store, next_next_kaddr)
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

pub fn apply_step(st: &ApplyState) -> State {
   let ApplyState { kaddr, store, .. } = st.clone();
   let kont_val = store.get(&kaddr).expect("Dont Got Kont");
   let kont = if let Val::Kont(k) = kont_val {
      k
   } else {
      panic!("Bad KAddr {:?}", kaddr)
   };
   match kont {
      Kont::Empty => State::Apply(st.clone()), // fixpoint!
      k @ Kont::If(..) => handle_if_kont(k, st),
      k @ Kont::Let(..) => handle_let_kont(k, st),
      k @ Kont::Prim(..) => handle_prim_kont(k, st),
      k @ Kont::ApplyPrim(..) => handle_apply_prim_kont(k, st),
      k @ Kont::Callcc(..) => handle_callcc_kont(k, st),
      k @ Kont::Set(..) => handle_set_bang_kont(k, st),
      k @ Kont::ApplyList(..) => handle_apply_list_kont(k, st),
      k @ Kont::App(..) => handle_app(k, st),
   }
}

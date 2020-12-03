//!
//! Items to do with 'apply states'

use crate::common::{make_scm_list, scm_list_to_vals, val_is_list};
use crate::common::{Alloc, CloType, Closure, Kont, SExpr, SExprState, State, Val, ValState};
use crate::prims::apply_prim;

fn handle_if_kont(k: Kont, st: &ValState) -> State {
   let ValState {
      ctrl: val,
      store,
      kstore,
      time,
      ..
   } = st.clone();
   if let Kont::If(et, ef, ifenv, next_kaddr) = k {
      let next_e = if val == Val::Boolean(false) { ef } else { et };
      State::Eval(SExprState::new(
         next_e, ifenv, store, kstore, next_kaddr, time,
      ))
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_let_kont(k: Kont, st: &ValState) -> State {
   let ValState {
      ctrl: val,
      store,
      kstore,
      ..
   } = st.clone();
   if let Kont::Let(vars, mut done, mut todo, eb, letenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let next_time = st.tick(vars.len() as u64);
         let mut next_env = letenv;
         let mut next_store = store;
         for (i, (bndvar, val)) in vars.iter().zip(done.iter()).enumerate() {
            let addr = st.alloc(i as u64);
            next_env = next_env.insert(bndvar.clone(), addr.clone());
            next_store = next_store.insert(addr, val.clone());
         }
         State::Eval(SExprState::new(
            eb, next_env, next_store, kstore, next_kaddr, next_time,
         ))
      } else {
         let head = todo.remove(0);
         let next_next_kaddr = st.alloc(0);
         let next_time = st.tick(1);
         let next_k = Kont::Let(vars, done, todo, eb, letenv.clone(), next_kaddr);
         let next_kstore = kstore.insert(next_next_kaddr.clone(), next_k);
         State::Eval(SExprState::new(
            head,
            letenv,
            store,
            next_kstore,
            next_next_kaddr,
            next_time,
         ))
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_prim_kont(k: Kont, st: &ValState) -> State {
   let ValState {
      ctrl: val,
      store,
      kstore,
      time,
      ..
   } = st.clone();
   if let Kont::Prim(op, mut done, mut todo, primenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let val = apply_prim(op, &done);
         State::Apply(ValState::new(val, store, kstore, next_kaddr, time))
      } else {
         let head = todo.remove(0);
         let next_next_kaddr = st.alloc(0);
         let next_time = st.tick(1);
         let next_k = Kont::Prim(op, done, todo, primenv.clone(), next_kaddr);
         let next_kstore = kstore.insert(next_next_kaddr.clone(), next_k);
         State::Eval(SExprState::new(
            head,
            primenv,
            store,
            next_kstore,
            next_next_kaddr,
            next_time,
         ))
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_apply_prim_kont(k: Kont, st: &ValState) -> State {
   let ValState {
      ctrl: val,
      store,
      kstore,
      time,
      ..
   } = st.clone();
   if let Kont::ApplyPrim(op, next_kaddr) = k {
      if !val_is_list(&val) {
         panic!("Apply not given a list.");
      }
      let val = apply_prim(op, &scm_list_to_vals(val));
      State::Apply(ValState::new(val, store, kstore, next_kaddr, time))
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_callcc_kont(k: Kont, st: &ValState) -> State {
   let ValState {
      ctrl: val,
      store,
      kstore,
      ..
   } = st.clone();
   if let Kont::Callcc(ref next_kaddr) = k {
      if let Val::Closure(Closure(clotype, body, cloenv)) = val {
         match clotype {
            CloType::MultiArg(mut params) => {
               if params.len() != 1 {
                  panic!("call/cc lambda only takes 1 argument!");
               }
               let addr = st.alloc(0);
               let next_time = st.tick(1);
               let next_k = kstore.get(next_kaddr).expect("K doesnt exist...?");
               let next_env = cloenv.insert(params.remove(0), addr.clone());
               let next_store = store.insert(addr, Val::Kont(next_k));
               State::Eval(SExprState::new(
                  body,
                  next_env,
                  next_store,
                  kstore,
                  next_kaddr.clone(),
                  next_time,
               ))
            }
            CloType::VarArg(_) => {
               panic!("call/cc takes a multi-arg lambda, not vararg");
            }
         }
      } else if let Val::Kont(kv) = val {
         let next_kaddr = st.alloc(0);
         let next_time = st.tick(1);
         let next_kstore = kstore.insert(next_kaddr.clone(), kv);
         State::Apply(ValState::new(
            Val::Kont(k.clone()),
            store,
            next_kstore,
            next_kaddr,
            next_time,
         ))
      } else {
         panic!("Call/cc given wrong type of argument.");
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_set_bang_kont(k: Kont, st: &ValState) -> State {
   let ValState {
      ctrl: val,
      store,
      kstore,
      time,
      ..
   } = st.clone();
   if let Kont::Set(addr, next_kaddr) = k {
      let next_store = store.insert(addr, val);
      State::Apply(ValState::new(
         Val::Void,
         next_store,
         kstore,
         next_kaddr,
         time,
      ))
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_apply_list_kont(k: Kont, st: &ValState) -> State {
   let ValState {
      ctrl: val,
      store,
      kstore,
      ..
   } = st.clone();
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

               let next_time = st.tick(args.len() as u64);
               let mut next_env = cloenv;
               let mut next_store = store;
               for (i, (arg, argval)) in args.iter().zip(argvals.iter()).enumerate() {
                  let addr = st.alloc(i as u64);
                  next_env = next_env.insert(arg.clone(), addr.clone());
                  next_store = next_store.insert(addr, argval.clone());
               }
               State::Eval(SExprState::new(
                  body, next_env, next_store, kstore, next_kaddr, next_time,
               ))
            } else if let Val::Closure(Closure(CloType::VarArg(arg), body, cloenv)) = *func {
               let next_time = st.tick(1);
               let addr = st.alloc(0);
               let next_env = cloenv.insert(arg, addr.clone());
               let next_store = store.insert(addr, val);
               State::Eval(SExprState::new(
                  body, next_env, next_store, kstore, next_kaddr, next_time,
               ))
            } else {
               panic!("Not given a function in `(apply func arglist)`");
            }
         }
         None => {
            let next_next_kaddr = st.alloc(0);
            let next_time = st.tick(1);
            let next_k = Kont::ApplyList(
               Some(Box::new(val)),
               SExpr::Atom("".into()),
               applyenv.clone(),
               next_kaddr,
            );
            let next_kstore = kstore.insert(next_next_kaddr.clone(), next_k);
            State::Eval(SExprState::new(
               arglist,
               applyenv,
               store,
               next_kstore,
               next_next_kaddr,
               next_time,
            ))
         }
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_app(k: Kont, st: &ValState) -> State {
   let ValState {
      ctrl: val,
      store,
      kstore,
      ..
   } = st.clone();
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
                  let next_time = st.tick(params.len() as u64);
                  let mut next_env = cloenv;
                  let mut next_store = store;
                  for (i, (param, arg)) in params.iter().zip(args.iter()).enumerate() {
                     let addr = st.alloc(i as u64);
                     next_env = next_env.insert(param.clone(), addr.clone());
                     next_store = next_store.insert(addr, arg.clone());
                  }
                  State::Eval(SExprState::new(
                     body, next_env, next_store, kstore, next_kaddr, next_time,
                  ))
               }
               CloType::VarArg(vararg) => {
                  let scm_list = make_scm_list(args);
                  let next_time = st.tick(1);
                  let addr = st.alloc(0);
                  let next_env = cloenv.insert(vararg, addr.clone());
                  let next_store = store.insert(addr, scm_list);
                  State::Eval(SExprState::new(
                     body, next_env, next_store, kstore, next_kaddr, next_time,
                  ))
               }
            }
         } else if let Val::Kont(kv) = head {
            if args.len() != 1 {
               panic!("applying a kont only takes 1 argument.");
            }
            // replace the current continuation with the stored one.
            let next_next_kaddr = st.alloc(0);
            let next_time = st.tick(1);
            let next_kstore = kstore.insert(next_next_kaddr.clone(), kv);
            State::Apply(ValState::new(
               args.remove(0),
               store,
               next_kstore,
               next_next_kaddr,
               next_time,
            ))
         } else {
            panic!("Closure wasnt head of application");
         }
      } else {
         let head = todo.remove(0);
         let next_next_kaddr = st.alloc(0);
         let next_time = st.tick(1);
         let next_kont = Kont::App(done, todo, appenv.clone(), next_kaddr);
         let next_kstore = kstore.insert(next_next_kaddr.clone(), next_kont);
         State::Eval(SExprState::new(
            head,
            appenv,
            store,
            next_kstore,
            next_next_kaddr,
            next_time,
         ))
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

pub fn apply_step(st: &ValState) -> State {
   let ValState { kaddr, kstore, .. } = st.clone();
   let kont = kstore.get(&kaddr).expect("Dont Got Kont");
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

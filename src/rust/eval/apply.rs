//!
//! Items to do with 'apply states'

use crate::common::{make_scm_list, scm_list_to_vals, val_is_list};
use crate::common::{Alloc, CloType, Closure, Kont, SExprState, State, Store, Val, ValState};
use crate::prims::apply_prim;

fn handle_if_kont(k: Kont, st: &ValState) -> State {
   let ValState { ctrl: val, .. } = st.clone();
   if let Kont::If(et, ef, ifenv, next_kaddr) = k {
      if val == Val::Boolean(false) {
         State::Eval(SExprState::new(ef, ifenv, next_kaddr, st.tick(1)))
      } else {
         State::Eval(SExprState::new(et, ifenv, next_kaddr, st.tick(1)))
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_let_kont(k: Kont, st: &ValState, store: &mut Store) -> State {
   let ValState { ctrl: val, .. } = st.clone();
   if let Kont::Let(vars, mut done, mut todo, eb, letenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let mut newenv = letenv;
         for (i, (bndvar, val)) in vars.iter().zip(done.iter()).enumerate() {
            let bnd_addr = store.add_to_store_offset(val.clone(), st, i as u64);
            newenv = newenv.insert(bndvar.clone(), bnd_addr.clone());
         }
         State::Eval(SExprState::new(
            eb,
            newenv,
            next_kaddr,
            st.tick(1 + (vars.len() as u64)),
         ))
      } else {
         let head = todo.remove(0);
         let new_kont = Kont::Let(vars, done, todo, eb, letenv.clone(), next_kaddr);
         let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
         State::Eval(SExprState::new(head, letenv, next_kaddr, st.tick(1)))
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_prim_kont(k: Kont, st: &ValState, store: &mut Store) -> State {
   let ValState { ctrl: val, .. } = st.clone();
   if let Kont::Prim(op, mut done, mut todo, primenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let val = apply_prim(op, &done);
         State::Apply(ValState::new(val, primenv, next_kaddr, st.tick(1)))
      } else {
         let head = todo.remove(0);
         let new_kont = Kont::Prim(op, done, todo, primenv.clone(), next_kaddr);
         let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
         State::Eval(SExprState::new(head, primenv, next_kaddr, st.tick(1)))
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_apply_prim_kont(k: Kont, st: &ValState) -> State {
   let ValState { ctrl: val, .. } = st.clone();
   if let Kont::ApplyPrim(op, aprimenv, next_kaddr) = k {
      if !val_is_list(&val) {
         panic!("Apply not given a list.");
      }
      let val = apply_prim(op, &scm_list_to_vals(val));
      State::Apply(ValState::new(val, aprimenv, next_kaddr, st.tick(1)))
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_callcc_kont(k: Kont, st: &ValState, store: &mut Store) -> State {
   let ValState { ctrl: val, .. } = st.clone();
   if let Kont::Callcc(ref callccenv, ref next_kaddr) = k {
      if let Val::Closure(Closure(clotype, body, cloenv)) = val {
         match clotype {
            CloType::MultiArg(params) => {
               if params.len() != 1 {
                  panic!("call/cc lambda only takes 1 argument!");
               }
               State::Eval(SExprState::new(
                  body,
                  cloenv.insert(params[0].clone(), next_kaddr.clone()),
                  next_kaddr.clone(),
                  st.tick(1),
               ))
            }
            CloType::VarArg(_) => {
               panic!("call/cc takes a multi-arg lambda, not vararg");
            }
         }
      } else if let Val::Kont(..) = val {
         let valaddr = store.add_to_store(val, st);
         State::Apply(ValState::new(
            Val::Kont(k.clone()),
            callccenv.clone(),
            valaddr,
            st.tick(1),
         ))
      } else {
         panic!("Call/cc given wrong type of argument.");
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_set_bang_kont(k: Kont, st: &ValState, store: &mut Store) -> State {
   let ValState { ctrl: val, .. } = st.clone();
   if let Kont::Set(var, setenv, next_kaddr) = k {
      let addr = match setenv.get(var.clone()) {
         Some(v) => v,
         None => panic!("{:?} was not defined.", var),
      };
      store.set(addr, val);
      State::Apply(ValState::new(Val::Void, setenv, next_kaddr, st.tick(1)))
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_apply_list_kont(k: Kont, st: &ValState, store: &mut Store) -> State {
   let ValState { ctrl: val, .. } = st.clone();
   if let Kont::ApplyList(maybe_func, arglist, applyenv, next_kaddr) = k {
      match maybe_func {
         None => {
            let new_kont = Kont::ApplyList(
               Some(Box::new(val)),
               arglist.clone(),
               applyenv.clone(),
               next_kaddr,
            );
            let kont_addr = store.add_to_store(Val::Kont(new_kont), st);
            State::Eval(SExprState::new(arglist, applyenv, kont_addr, st.tick(1)))
         }
         Some(func) => {
            if !val_is_list(&val) {
               panic!("Apply not given a list.");
            }
            if let Val::Closure(Closure(CloType::MultiArg(args), body, cloenv)) = *func {
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
               let mut newenv = cloenv;
               for (i, (arg, argval)) in args.iter().zip(argvals.iter()).enumerate() {
                  let argval_addr = store.add_to_store_offset(argval.clone(), st, i as u64);
                  newenv = newenv.insert(arg.clone(), argval_addr.clone());
               }
               State::Eval(SExprState::new(
                  body,
                  newenv,
                  next_kaddr,
                  st.tick(args.len() as u64),
               ))
            } else if let Val::Closure(Closure(CloType::VarArg(arg), body, cloenv)) = *func {
               let addr = store.add_to_store(val, st);
               let newenv = cloenv.insert(arg, addr);
               State::Eval(SExprState::new(body, newenv, next_kaddr, st.tick(1)))
            } else {
               panic!("Not given a function in `(apply func arglist)`");
            }
         }
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_app(k: Kont, st: &ValState, store: &mut Store) -> State {
   let ValState { ctrl: val, .. } = st.clone();
   if let Kont::App(mut done, mut todo, appenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let head = done.remove(0);
         let args = done;
         if let Val::Closure(Closure(clotype, body, cloenv)) = head {
            match clotype {
               CloType::MultiArg(params) => {
                  if params.len() != args.len() {
                     panic!("arg # mismatch.");
                  }
                  let mut newenv = cloenv;
                  for (i, (param, arg)) in params.iter().zip(args.iter()).enumerate() {
                     let param_addr = store.add_to_store_offset(arg.clone(), st, i as u64);
                     newenv = newenv.insert(param.clone(), param_addr.clone());
                  }
                  State::Eval(SExprState::new(
                     body,
                     newenv,
                     next_kaddr,
                     st.tick(params.len() as u64),
                  ))
               }
               CloType::VarArg(vararg) => {
                  let scm_list = make_scm_list(args.to_vec());
                  let addr = store.add_to_store(scm_list, st);
                  let newenv = cloenv.insert(vararg, addr);
                  State::Eval(SExprState::new(body, newenv, next_kaddr, st.tick(1)))
               }
            }
         } else if let k @ Val::Kont(..) = head {
            if args.len() != 1 {
               panic!("applying a kont only takes 1 argument.");
            }

            // replace the current continuation with the stored one.
            let new_kaddr = store.add_to_store(k, st);
            State::Apply(ValState::new(
               args[0].clone(),
               appenv,
               new_kaddr,
               st.tick(1),
            ))
         } else {
            panic!("Closure wasnt head of application");
         }
      } else {
         let head = todo.remove(0);
         let new_kont = Kont::App(done, todo, appenv.clone(), next_kaddr);
         let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
         State::Eval(SExprState::new(head, appenv, next_kaddr, st.tick(1)))
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

pub fn apply_step(st: &ValState, store: &mut Store) -> State {
   let ValState { kont_addr, .. } = st.clone();
   let kontval = store.get(kont_addr).expect("Dont Got Kont");
   if let Val::Kont(kont) = kontval {
      match kont {
         Kont::Empty => State::Apply(st.clone()), // fixpoint!
         k @ Kont::If(..) => handle_if_kont(k, st),
         k @ Kont::Let(..) => handle_let_kont(k, st, store),
         k @ Kont::Prim(..) => handle_prim_kont(k, st, store),
         k @ Kont::ApplyPrim(..) => handle_apply_prim_kont(k, st),
         k @ Kont::Callcc(..) => handle_callcc_kont(k, st, store),
         k @ Kont::Set(..) => handle_set_bang_kont(k, st, store),
         k @ Kont::ApplyList(..) => handle_apply_list_kont(k, st, store),
         k @ Kont::App(..) => handle_app(k, st, store),
      }
   } else {
      panic!("kont_addr not a kont addr!");
   }
}

//!
//! Items to do with 'apply states'.
//! Apply states are evaluating the current-continuation
//! because the control is a value.

use crate::common::{
   apply_state, balloc, eval_state, kalloc, make_scm_list, val_maybe_list, ApplyState, CloType,
   Closure, ConcreteVal, Expr, Kont, State, Val,
};
use crate::prims::apply_prim;

fn handle_if_kont(k: Kont, st: &ApplyState) -> im::HashSet<State> {
   let ApplyState { val, store, .. } = st.clone();

   if let Kont::If(et, ef, ifenv, next_kaddr) = k {
      let fals = im::HashSet::unit(eval_state(
         ef,
         ifenv.clone(),
         store.clone(),
         next_kaddr.clone(),
      ));
      let tru = im::HashSet::unit(eval_state(et, ifenv, store, next_kaddr));
      let both = fals.clone().union(tru.clone());

      // we are able to run the false branch only when we only ever see #f
      // we are able to run the true branch only when we never could see #f
      // otherwise, run both.
      if let Ok(ConcreteVal::Boolean(false)) = val.vals {
         // if its false but we have closures too, then we need both branches.
         if val.closures.is_empty() {
            fals
         } else {
            both
         }
      } else if let Ok(..) = val.vals {
         tru
      } else if let Err(false) = val.vals {
         // in bottom, we only have closures, which are truthy.
         tru
      } else {
         // only case left is top, we need to run both.
         both
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_let_kont(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::Let(ctx, vars, mut done, mut todo, eb, letenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let mut next_env = letenv;
         let mut next_store = store;
         for (bndvar, val) in vars.iter().zip(done.iter()) {
            let addr = balloc(bndvar.clone(), ctx.clone());
            next_env = next_env.insert(bndvar.clone(), addr.clone());
            next_store = next_store.insert(addr, val.clone());
         }
         eval_state(eb, next_env, next_store, next_kaddr)
      } else {
         let head = todo.remove(0);
         let next_next_kaddr = kalloc(head.clone(), letenv.clone());
         let next_k = Kont::Let(ctx, vars, done, todo, eb, letenv.clone(), next_kaddr);
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
         let val = apply_prim(op, &make_scm_list(done));
         apply_state(val, store, next_kaddr)
      } else {
         let head = todo.remove(0);
         // TODO: should I use the same control here? AKA same kaddr?
         let next_next_kaddr = kalloc(head.clone(), primenv.clone());
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
      if matches!(val_maybe_list(&val), Some(false)) {
         panic!("Apply not given a list.");
      }
      let val = apply_prim(op, &val);
      apply_state(val, store, next_kaddr)
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_callcc_kont(k: Kont, st: &ApplyState) -> im::HashSet<State> {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::Callcc(ref ctx, ref next_kaddr) = k {
      // TODO: do I just ignore the possible values in `val.vals`? And deal only with `.closures`?
      // And what do I do about the (call/cc k) case??? if k is top, then WUTDO???
      // ugh

      val.closures
         .into_iter()
         .fold(
            im::HashSet::new(),
            |accum, Closure(clotype, body, cloenv)| {
               accum.union(match clotype {
                  CloType::MultiArg(mut params) => {
                     if params.len() != 1 {
                        panic!("call/cc lambda only takes 1 argument!");
                     }
                     let parameter = params.remove(0);
                     let addr = balloc(parameter.clone(), ctx.clone());
                     let next_ks = store.getk(next_kaddr);
                     next_ks
                        .into_iter()
                        .map(|next_k| {
                           let next_env = cloenv.insert(parameter.clone(), addr.clone());
                           let next_store =
                              store.insert(addr.clone(), Val::new(ConcreteVal::Kont(next_k)));
                           eval_state(body.clone(), next_env, next_store, next_kaddr.clone())
                        })
                        .collect()
                  }
                  CloType::VarArg(_) => {
                     panic!("call/cc takes a multi-arg lambda, not vararg");
                  }
               })
            },
         )
         .union(if let Ok(ConcreteVal::Kont(k)) = val.vals {
            // reuse the same addr because there is no expression to make a new allocation.
            // but thats okay cause this is an AAM so addrs can be conflated.
            let next_store = store.insertk(next_kaddr.clone(), k.clone());
            im::HashSet::unit(apply_state(
               Val::new(ConcreteVal::Kont(k)),
               next_store,
               next_kaddr.clone(),
            ))
         } else {
            // if its not a guaranteed continuation, we just bail out I guess...
            im::HashSet::new()
         })
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_set_bang_kont(k: Kont, st: &ApplyState) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::Set(addr, next_kaddr) = k {
      let next_store = store.insert(addr, val);
      apply_state(Val::new(ConcreteVal::Void), next_store, next_kaddr)
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

fn handle_apply_list_kont(k: Kont, st: &ApplyState) -> im::HashSet<State> {
   let ApplyState { val, store, .. } = st.clone();
   // todo `(apply k (list arg))` support? (applying a kont with a list?)
   if let Kont::ApplyList(ctx, maybe_func, arglist, applyenv, next_kaddr) = k {
      match maybe_func {
         Some(func) => {
            if matches!(val_maybe_list(&val), Some(false)) {
               panic!("Apply not given a list.");
            }
            // TODO: should I just ignore func.vals here?
            // and if no closures are in the func (which should be an error)
            // would it be better to silently fail by returning no states,
            // or error out / put a message?
            func
               .closures
               .into_iter()
               .fold(im::HashSet::new(), |accum, cv| {
                  accum.update(match cv {
                     Closure(CloType::MultiArg(args), body, cloenv) => {
                        let mut next_env = cloenv;
                        let mut next_store = store.clone();
                        let mut cur = val.clone();
                        for expected in args.into_iter() {
                           // TODO: worry about the clos???
                           let argval = match cur.vals {
                              Err(false) => {
                                 // current value is a closure, not a proper list element.
                                 panic!("Not given a proper list somehow.");
                              }
                              Err(true) => {
                                 // TODO: i think this is wrong??? Look into it.
                                 cur.clone() // top, so just use cur so we keep the closures.
                              }
                              Ok(ConcreteVal::Cons(ref car, _)) => *car.clone(),
                              Ok(other) => {
                                 panic!("Not enough args. given {:?}", other);
                              }
                           };
                           let addr = balloc(expected.clone(), ctx.clone());
                           next_env = next_env.insert(expected, addr.clone());
                           next_store = next_store.insert(addr, argval);
                           cur = match cur.vals {
                              Ok(ConcreteVal::Cons(_, cdr)) => *cdr,
                              _ => cur.clone(),
                           };
                        }
                        // TODO: check if cur is Null to ensure not too many args given?
                        //       wut do if Cur is Err?

                        eval_state(body, next_env, next_store, next_kaddr.clone())
                     }
                     Closure(CloType::VarArg(arg), body, cloenv) => {
                        let addr = balloc(arg.clone(), ctx.clone());
                        let next_env = cloenv.insert(arg, addr.clone());
                        let next_store = store.insert(addr, val.clone());
                        eval_state(body, next_env, next_store, next_kaddr.clone())
                     }
                  })
               })
         }
         None => {
            // TODO: should this be the ctx? AKA same kaddr as the original Kont::ApplyList?
            let next_next_kaddr = kalloc(arglist.clone(), applyenv.clone());
            let next_k = Kont::ApplyList(
               ctx,
               Some(Box::new(val)),
               Expr::Atom("".into()),
               applyenv.clone(),
               next_kaddr,
            );
            let next_store = store.insertk(next_next_kaddr.clone(), next_k);
            im::HashSet::unit(eval_state(arglist, applyenv, next_store, next_next_kaddr))
         }
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

// regular untagged application.
fn handle_app(k: Kont, st: &ApplyState) -> im::HashSet<State> {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::App(ctx, mut done, mut todo, appenv, next_kaddr) = k {
      done.push(val);
      if todo.is_empty() {
         let headfn = done.remove(0);
         let mut args = done;
         headfn
            .closures
            .into_iter()
            .fold(
               im::HashSet::new(),
               |accum, Closure(clotype, body, cloenv)| {
                  accum.update(match clotype {
                     CloType::MultiArg(params) => {
                        if params.len() != args.len() {
                           panic!("arg # mismatch.");
                        }
                        let mut next_env = cloenv;
                        let mut next_store = store.clone();
                        for (param, arg) in params.iter().zip(args.iter()) {
                           let addr = balloc(param.clone(), ctx.clone());
                           next_env = next_env.insert(param.clone(), addr.clone());
                           next_store = next_store.insert(addr, arg.clone());
                        }
                        eval_state(body, next_env, next_store, next_kaddr.clone())
                     }
                     CloType::VarArg(vararg) => {
                        let scm_list = make_scm_list(args.clone());
                        let addr = balloc(vararg.clone(), ctx.clone());
                        let next_env = cloenv.insert(vararg, addr.clone());
                        let next_store = store.insert(addr, scm_list);
                        eval_state(body, next_env, next_store, next_kaddr.clone())
                     }
                  })
               },
            )
            .union(match headfn.vals {
               Ok(ConcreteVal::Kont(kv)) => {
                  if args.len() != 1 {
                     panic!("applying a kont only takes 1 argument.");
                  }
                  let kont_arg = args.remove(0);
                  // Replace the current continuation with the stored one.
                  // Reuse the same address though,
                  // because this is an abstract machine and i can do that.
                  // also, we dont have an expr to make a new kaddr from...]
                  let next_store = store.insertk(next_kaddr.clone(), kv);
                  im::HashSet::unit(apply_state(kont_arg, next_store, next_kaddr))
               }
               // in top, we dont have any info
               // in bottom, it cant be a kont, as it was never inhabited.
               // in non-kont, we just ignore.
               _ => im::HashSet::new(),
            })
      } else {
         let head = todo.remove(0);
         let next_next_kaddr = kalloc(head.clone(), appenv.clone());
         let next_kont = Kont::App(ctx, done, todo, appenv.clone(), next_kaddr);
         let next_store = store.insertk(next_next_kaddr.clone(), next_kont);
         im::HashSet::unit(eval_state(head, appenv, next_store, next_next_kaddr))
      }
   } else {
      panic!("Given Wrong Kontinuation");
   }
}

pub fn apply_step(st: &ApplyState) -> im::HashSet<State> {
   let ApplyState { kaddr, store, .. } = st.clone();
   let konts = store.getk(&kaddr);
   konts
      .into_iter()
      .map(|kont| match kont {
         Kont::Empty => im::HashSet::new(), // fixpoint! no new states.
         k @ Kont::If(..) => handle_if_kont(k, st),
         k @ Kont::Let(..) => im::HashSet::unit(handle_let_kont(k, st)),
         k @ Kont::Prim(..) => im::HashSet::unit(handle_prim_kont(k, st)),
         k @ Kont::ApplyPrim(..) => im::HashSet::unit(handle_apply_prim_kont(k, st)),
         k @ Kont::Callcc(..) => handle_callcc_kont(k, st),
         k @ Kont::Set(..) => im::HashSet::unit(handle_set_bang_kont(k, st)),
         k @ Kont::ApplyList(..) => handle_apply_list_kont(k, st),
         k @ Kont::App(..) => handle_app(k, st),
      })
      .fold(im::HashSet::new(), |accum, n| accum.union(n))
}

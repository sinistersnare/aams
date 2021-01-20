//! Handles apply states, which applies a value relative to the current continuation.

use crate::common::{find_frees, Expr, LambdaArgType, Prim, Var};
use crate::flat_abstract::domains::{
   ApplyState, BAddr, Closure, Env, InnerVal, KAddr, Kont, State, Store, Val,
};
use crate::flat_abstract::prims::{apply_prim, PRIMS};

fn make_scm_list(vals: Vec<Val>) -> Val {
   let mut lst = Val::from(InnerVal::Null);
   for v in vals.into_iter().rev() {
      lst = Val::from(InnerVal::Cons(Box::new(v), Box::new(lst)));
   }
   lst
}

// val should be a cons list.
fn vec_from_val(val: Val) -> Option<Vec<Val>> {
   let mut vec = vec![];
   let mut cur = match val.inner_val.clone() {
      Err(_) => {
         // TODO:
         // not sure what to do in this case...
         return None;
      }
      Ok(iv) => iv,
   };
   loop {
      match cur {
         InnerVal::Null => {
            break;
         }
         InnerVal::Cons(car, cdr) => {
            vec.push(*car);
            cur = match cdr.inner_val {
               Err(_) => {
                  // TODO: same as above
                  return None;
               }
               Ok(iv) => iv,
            };
         }
         _ => {
            panic!("Not given a proper list: {:?}", val);
         }
      }
   }
   Some(vec)
}

fn call_clo_helper(
   clo: Closure,
   arg_vals: Vec<Val>,
   env: Env,
   store: Store,
   ctx: Expr,
   kaddr: KAddr,
) -> State {
   let bound_prims: im::HashSet<Var> = PRIMS.keys().map(|p| Var(p.to_string())).collect();
   match clo {
      Closure(LambdaArgType::FixedArg(args), body, lamenv) => {
         let next_env = env.next(ctx);
         let arg_addrs = args
            .clone()
            .into_iter()
            .map(|var| BAddr(var, next_env.clone()));
         let bound_args = args.into_iter().collect();
         let free_vars = find_frees(body.clone(), bound_prims + bound_args);
         let free_addrs = free_vars
            .clone()
            .into_iter()
            .map(|v| BAddr(v, next_env.clone()));
         let next_store = arg_addrs
            .zip(arg_vals.into_iter())
            .fold(store.clone(), |s, (k, v)| s.join(k, v));
         let free_vals = free_vars
            .into_iter()
            .map(|fv| store.get(&BAddr(fv, lamenv.clone())));
         let next_store = free_addrs
            .zip(free_vals)
            .fold(next_store, |s, (k, v)| s.join(k, v));
         State::eval(body, next_env, next_store, kaddr)
      }
      Closure(LambdaArgType::VarArg(arg), body, lamenv) => {
         let arg_vals = make_scm_list(arg_vals);
         let next_env = env.next(ctx);
         let arg_addr = BAddr(arg.clone(), next_env.clone());
         let free_vars = find_frees(body.clone(), bound_prims + im::HashSet::unit(arg));
         let free_addrs = free_vars
            .clone()
            .into_iter()
            .map(|var| BAddr(var, next_env.clone()));
         let next_store = free_addrs
            .zip(
               free_vars
                  .into_iter()
                  .map(|fv| store.get(&BAddr(fv, lamenv.clone()))),
            )
            .fold(store.join(arg_addr, arg_vals), |s, (k, v)| s.join(k, v));
         State::eval(body, next_env, next_store, kaddr)
      }
   }
}

fn call_prim_helper(prim: Prim, arg_vals: Vec<Val>, env: Env, store: Store, kaddr: KAddr) -> State {
   let v = apply_prim(prim, &arg_vals);
   State::apply(v, env, store, kaddr)
}

fn call_kont_helper(k: Kont, mut arg_vals: Vec<Val>, env: Env, store: Store, ctx: Expr) -> State {
   let arg = arg_vals.remove(0);
   if !arg_vals.is_empty() {
      panic!(
         "continuation given wrong number of args: {:?}",
         arg_vals.len() + 1
      );
   }
   let kaddr = KAddr(ctx, env.clone());
   let next_store = store.joink(kaddr.clone(), k);
   State::apply(arg, env, next_store, kaddr)
}

fn call_helper(
   val: Val,
   args: Vec<Val>,
   env: Env,
   store: Store,
   ctx: Expr,
   next_kaddr: KAddr,
) -> im::HashSet<State> {
   let konts = val.kontinuations;
   let prims = val.primitives;
   let clos = val.closures;
   let kstates: im::HashSet<State> = konts
      .into_iter()
      .map(|k| call_kont_helper(k, args.clone(), env.clone(), store.clone(), ctx.clone()))
      .collect();
   let pstates: im::HashSet<State> = prims
      .into_iter()
      .map(|p| {
         call_prim_helper(
            p,
            args.clone(),
            env.clone(),
            store.clone(),
            next_kaddr.clone(),
         )
      })
      .collect();
   let cstates: im::HashSet<State> = clos
      .into_iter()
      .map(|c| {
         call_clo_helper(
            c,
            args.clone(),
            env.clone(),
            store.clone(),
            ctx.clone(),
            next_kaddr.clone(),
         )
      })
      .collect();
   kstates + pstates + cstates
}

fn handle_if(st: &ApplyState, kont: Kont) -> im::HashSet<State> {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::If(et, ef, ifenv, next_kaddr) = kont {
      let false_branch = im::HashSet::unit(State::eval(
         ef,
         ifenv.clone(),
         store.clone(),
         next_kaddr.clone(),
      ));
      let true_branch = im::HashSet::unit(State::eval(et, ifenv, store, next_kaddr));
      let both_branches = false_branch.clone().union(true_branch.clone());
      if val.is_falsy() {
         false_branch
      } else if val.is_truthy() {
         true_branch
      } else {
         both_branches
      }
   } else {
      panic!("DONT GIVE ME THE WRONG KONT {:?}", kont);
   }
}

fn handle_set(st: &ApplyState, kont: Kont) -> State {
   let ApplyState {
      val, env, store, ..
   } = st.clone();
   if let Kont::Set(addr, next_kaddr) = kont {
      let next_store = store.join(addr, val);
      State::apply(Val::from(InnerVal::Void), env, next_store, next_kaddr)
   } else {
      panic!("DONT GIVE ME THE WRONG KONT {:?}", kont);
   }
}

fn handle_callcc(st: &ApplyState, kont: Kont) -> im::HashSet<State> {
   let ApplyState {
      val, env, store, ..
   } = st.clone();
   if let Kont::Callcc(ctx, next_kaddr) = kont {
      let konts = store.getk(&next_kaddr);
      konts
         .into_iter()
         .map(|k| {
            let args = vec![Val::from_kont(k)];
            call_helper(
               val.clone(),
               args,
               env.clone(),
               store.clone(),
               ctx.clone(),
               next_kaddr.clone(),
            )
         })
         .fold(im::HashSet::new(), |states, state| states + state)
   } else {
      panic!("DONT GIVE ME THE WRONG KONT {:?}", kont);
   }
}

fn handle_apply(st: &ApplyState, kont: Kont) -> im::HashSet<State> {
   let ApplyState {
      val, env, store, ..
   } = st.clone();
   if let Kont::Apply(applyexpr, None, e, kontenv, next_kaddr) = kont {
      let next_next_kaddr = KAddr(applyexpr.clone(), kontenv.clone());
      let kont = Kont::Apply(
         applyexpr,
         Some(Box::new(val)),
         e.clone(),
         kontenv.clone(),
         next_kaddr,
      );
      let next_store = store.joink(next_next_kaddr.clone(), kont);
      im::HashSet::unit(State::eval(e, kontenv, next_store, next_next_kaddr))
   } else if let Kont::Apply(applyexpr, Some(vf), _, _, next_kaddr) = kont {
      if let Some(args) = vec_from_val(val) {
         call_helper(*vf, args, env, store, applyexpr, next_kaddr)
      } else {
         // Was not given a list, something like (apply f 12)
         // what monster would do that....
         // Im not worrying about error cases right now... so gonna leave this!
         im::HashSet::new()
      }
   } else {
      panic!("DONT GIVE ME THE WRONG KONT {:?}", kont);
   }
}

fn handle_call(st: &ApplyState, kont: Kont) -> im::HashSet<State> {
   let ApplyState {
      val, env, store, ..
   } = st.clone();
   if let Kont::Call(callexpr, mut done, mut todo, kontenv, next_kaddr) = kont {
      done.push(val);
      if todo.is_empty() {
         let vh = done.remove(0);
         call_helper(vh, done, env, store, callexpr, next_kaddr)
      } else {
         let head = todo.remove(0);
         let next_next_kaddr = KAddr(callexpr.clone(), kontenv.clone());
         let kont = Kont::Call(callexpr, done, todo, kontenv.clone(), next_kaddr);
         let next_store = store.joink(next_next_kaddr.clone(), kont);
         im::HashSet::unit(State::eval(head, kontenv, next_store, next_next_kaddr))
      }
   } else {
      panic!("DONT GIVE ME THE WRONG KONT {:?}", kont);
   }
}

pub fn apply_step(st: &ApplyState) -> im::HashSet<State> {
   let ApplyState { store, kaddr, .. } = st.clone();
   let konts = store.getk(&kaddr);
   konts
      .into_iter()
      .map(|kont| match kont {
         Kont::Empty => im::HashSet::unit(State::A(st.clone())),
         Kont::If(..) => handle_if(st, kont),
         Kont::Set(..) => im::HashSet::unit(handle_set(st, kont)),
         Kont::Callcc(..) => handle_callcc(st, kont),
         Kont::Apply(..) => handle_apply(st, kont),
         Kont::Call(..) => handle_call(st, kont),
      })
      .flatten()
      .collect()
}

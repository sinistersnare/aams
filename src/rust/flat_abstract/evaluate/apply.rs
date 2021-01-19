//! Handles apply states, which applies a value relative to the current continuation.

use crate::common::{Expr, LambdaArgType, Var};
use crate::matching::{Matching, match_syntax};
use crate::flat_abstract::domains::{
   ApplyState, BAddr, Closure, Env, KAddr, Kont, State, Store, Val,
};
use crate::flat_abstract::prims::{apply_prim, PRIMS};

fn find_frees(expr: Expr, bound: im::HashSet<Var>) -> im::Vector<Var> {
   match match_syntax(expr) {
      Matching::If(ec, et, ef) => {
         let ec_free = find_frees(ec, bound.clone());
         let et_free = find_frees(et, bound.clone());
         let ef_free = find_frees(ef, bound);
         ec_free + et_free + ef_free
      }
      Matching::Let(vars, exprs, eb) => {
         let bindings_free: im::Vector<Var> = exprs
            .into_iter()
            .map(|expr| find_frees(expr, bound.clone()))
            .flatten()
            .collect();
         bindings_free + find_frees(eb, bound + vars.into_iter().collect())
      }
      Matching::SetBang(var, expr) => {
         let var_free = if bound.contains(&var) {
            im::Vector::new()
         } else {
            im::Vector::unit(var)
         };
         var_free + find_frees(expr, bound)
      }
      Matching::Callcc(expr) => {
         find_frees(expr, bound)
      }
      Matching::Apply(ef, ea) => {
         find_frees(ef, bound.clone()) + find_frees(ea, bound)
      }
      Matching::Call(args) => {
         args
            .into_iter()
            .map(|expr| find_frees(expr, bound.clone()))
            .flatten()
            .collect()
      }
      Matching::Lambda(argtype, body) => {
         match argtype {
            LambdaArgType::FixedArg(args) => {
               find_frees(body, bound + args.into_iter().collect())
            }
            LambdaArgType::VarArg(arg) => find_frees(body, bound.update(arg)),
         }
      }
      Matching::StrAtom(a) => {
         let var = Var(a.clone());
         if PRIMS.contains_key(&*a) || bound.contains(&var) {
            im::Vector::new()
         } else {
            im::Vector::unit(var)
         }
      }
      Matching::Quote(..) | Matching::Number(..) | Matching::Boolean(..) => {
         im::Vector::new()
      }
   }
}

fn make_scm_list(vals: Vec<Val>) -> Val {
   let mut lst = Val::Null;
   for v in vals.into_iter().rev() {
      lst = Val::Cons(Box::new(v), Box::new(lst));
   }
   lst
}

// val should be a cons list.
fn vec_from_val(val: Val) -> Vec<Val> {
   let mut vec = vec![];
   let mut cur = val.clone();
   loop {
      match cur {
         Val::Null => {
            break;
         }
         Val::Cons(car, cdr) => {
            vec.push(*car);
            cur = *cdr;
         }
         _ => {
            panic!("Not given a proper list: {:?}", val);
         }
      }
   }
   vec
}

fn call_helper(
   head: Val,
   mut arg_vals: Vec<Val>,
   env: Env,
   store: Store,
   ctx: Expr,
   kaddr: KAddr,
) -> State {
   match head {
      Val::Closure(Closure(LambdaArgType::FixedArg(args), body, lamenv)) => {
         let next_env = env.next(ctx);
         let arg_addrs = args
            .clone()
            .into_iter()
            .map(|var| BAddr(var, next_env.clone()));
         let free_vars = find_frees(body.clone(), args.into_iter().collect());
         let free_addrs = free_vars
            .clone()
            .into_iter()
            .map(|var| BAddr(var, next_env.clone()));
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
      Val::Closure(Closure(LambdaArgType::VarArg(arg), body, lamenv)) => {
         let arg_vals = make_scm_list(arg_vals);
         let next_env = env.next(ctx);
         let arg_addr = BAddr(arg.clone(), next_env.clone());
         let free_vars = find_frees(body.clone(), im::HashSet::unit(arg));
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
      Val::Kont(k) => {
         let arg = arg_vals.remove(0);
         if !arg_vals.is_empty() {
            panic!(
               "continuation given wrong number of args: {:?}",
               arg_vals.len() + 1
            );
         }
         let kaddr = KAddr(store.count());
         let next_store = store.joink(kaddr.clone(), k);
         State::apply(arg, env, next_store, kaddr)
      }
      Val::Prim(prim) => {
         let v = apply_prim(prim, &arg_vals);
         State::apply(v, env, store, kaddr)
      }
      other => {
         panic!("Bad type for function call head. Given `{:?}`", other);
      }
   }
}

fn handle_if(st: &ApplyState, kont: Kont) -> State {
   let ApplyState { val, store, .. } = st.clone();
   if let Kont::If(et, ef, ifenv, next_kaddr) = kont {
      if val == Val::Boolean(false) {
         State::eval(ef, ifenv, store, next_kaddr)
      } else {
         State::eval(et, ifenv, store, next_kaddr)
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
      State::apply(Val::Void, env, next_store, next_kaddr)
   } else {
      panic!("DONT GIVE ME THE WRONG KONT {:?}", kont);
   }
}

fn handle_callcc(st: &ApplyState, kont: Kont) -> State {
   let ApplyState {
      val, env, store, ..
   } = st.clone();
   if let Kont::Callcc(ctx, next_kaddr) = kont {
      call_helper(
         val,
         vec![Val::Kont(store.getk(&next_kaddr))],
         env,
         store,
         ctx,
         next_kaddr,
      )
   } else {
      panic!("DONT GIVE ME THE WRONG KONT {:?}", kont);
   }
}

fn handle_apply(st: &ApplyState, kont: Kont) -> State {
   let ApplyState {
      val, env, store, ..
   } = st.clone();
   if let Kont::Apply(applyexpr, None, e, kontenv, next_kaddr) = kont {
      let next_next_kaddr = KAddr(store.count());
      let kont = Kont::Apply(
         applyexpr,
         Some(Box::new(val)),
         e.clone(),
         kontenv.clone(),
         next_kaddr,
      );
      let next_store = store.joink(next_next_kaddr.clone(), kont);
      State::eval(e, kontenv, next_store, next_next_kaddr)
   } else if let Kont::Apply(applyexpr, Some(vf), _, _, next_kaddr) = kont {
      call_helper(*vf, vec_from_val(val), env, store, applyexpr, next_kaddr)
   } else {
      panic!("DONT GIVE ME THE WRONG KONT {:?}", kont);
   }
}

fn handle_call(st: &ApplyState, kont: Kont) -> State {
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
         let next_next_kaddr = KAddr(store.count());
         let kont = Kont::Call(callexpr, done, todo, kontenv.clone(), next_kaddr);
         let next_store = store.joink(next_next_kaddr.clone(), kont);
         State::eval(head, kontenv, next_store, next_next_kaddr)
      }
   } else {
      panic!("DONT GIVE ME THE WRONG KONT {:?}", kont);
   }
}

pub fn apply_step(st: &ApplyState) -> im::HashSet<State> {
   let ApplyState { store, kaddr, .. } = st.clone();
   let kont = store.getk(&kaddr);
   match kont {
      Kont::Empty => State::A(st.clone()),
      Kont::If(..) => handle_if(st, kont),
      Kont::Set(..) => handle_set(st, kont),
      Kont::Callcc(..) => handle_callcc(st, kont),
      Kont::Apply(..) => handle_apply(st, kont),
      Kont::Call(..) => handle_call(st, kont),
   }
}

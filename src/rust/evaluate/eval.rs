//!
//! Items to do with 'eval states'
//! Those are states that deal with evaluating the control
//! to reach a value.

use crate::common::{
   eval_alloc, ApplyState, Closure, EvalState, Expr, Kont, Prim, State, Val, Var,
};

use crate::common::{matches_boolean, matches_number};
use crate::evaluate::matching::*; // just simple matching functions found in matching.rs
use crate::prims::apply_prim;

fn is_atomic(ctrl: &Expr) -> bool {
   match ctrl {
      Expr::List(ref list) => {
         matches!(matches_lambda_expr(list), Some(_)) || matches!(matches_quote_expr(list), Some(_))
      }
      Expr::Atom(_) => true,
   }
}

fn atomic_eval(
   EvalState {
      ctrl, env, store, ..
   }: &EvalState,
) -> Val {
   match ctrl {
      Expr::List(ref list) => {
         if let Some((args, body)) = matches_lambda_expr(list) {
            Val::Closure(Closure(args, body, env.clone()))
         } else if let Some(e) = matches_quote_expr(list) {
            Val::Quote(e)
         } else {
            panic!("Not given an atomic value, given some list.");
         }
      }
      Expr::Atom(ref atom) => {
         if let Some(n) = matches_number(atom) {
            Val::Number(n)
         } else if let Some(b) = matches_boolean(atom) {
            Val::Boolean(b)
         } else {
            store
               .get(&env.get(&Var(atom.clone())).expect("Atom not in env"))
               .expect("Atom not in store")
         }
      }
   }
}

fn handle_prim_expr(prim: Prim, mut args: Vec<Expr>, st: &EvalState) -> State {
   let EvalState {
      env,
      store,
      kstore,
      kaddr,
      ..
   } = st.clone();
   if args.is_empty() {
      let val = apply_prim(prim, &[]);
      State::Apply(ApplyState::new(val, store, kstore, kaddr))
   } else {
      let arg0 = args.remove(0);
      let next_kaddr = eval_alloc(st, 0);
      let next_k = Kont::Prim(
         prim,
         Vec::with_capacity(args.len()),
         args,
         env.clone(),
         kaddr,
      );
      let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
      State::Eval(EvalState::new(arg0, env, store, next_kstore, next_kaddr))
   }
}

fn handle_let_expr(vars: Vec<Var>, mut exprs: Vec<Expr>, eb: Expr, st: &EvalState) -> State {
   let EvalState {
      env,
      store,
      kstore,
      kaddr,
      ..
   } = st.clone();
   let len = vars.len();
   if len == 0 {
      // why would you write (let () eb) you heathen
      // because of you I have to cover this case
      State::Eval(EvalState::new(eb, env, store, kstore, kaddr))
   } else {
      let e0 = exprs.remove(0);
      let rest = exprs;
      let next_kaddr = eval_alloc(st, 0);
      let next_k = Kont::Let(vars, Vec::with_capacity(len), rest, eb, env.clone(), kaddr);
      let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
      State::Eval(EvalState::new(e0, env, store, next_kstore, next_kaddr))
   }
}

fn handle_function_application_expr(list: &[Expr], st: &EvalState) -> State {
   let EvalState {
      env,
      store,
      kstore,
      kaddr,
      ..
   } = st.clone();
   let mut args = list.to_vec();
   let func = args.remove(0);

   let next_kaddr = eval_alloc(st, 0);
   let next_k = Kont::App(Vec::with_capacity(list.len()), args, env.clone(), kaddr);
   let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
   State::Eval(EvalState::new(func, env, store, next_kstore, next_kaddr))
}

pub fn eval_step(st: &EvalState) -> State {
   let EvalState {
      ctrl,
      store,
      kstore,
      env,
      kaddr,
      ..
   } = st.clone();
   if is_atomic(&ctrl) {
      let val = atomic_eval(st);
      State::Apply(ApplyState::new(val, store, kstore, kaddr))
   } else {
      match ctrl {
         Expr::List(ref list) => {
            if let Some((ec, et, ef)) = matches_if_expr(list) {
               let next_kaddr = eval_alloc(st, 0);
               let next_k = Kont::If(et, ef, env.clone(), kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(EvalState::new(ec, env, store, next_kstore, next_kaddr))
            } else if let Some((vars, exprs, eb)) = matches_let_expr(list) {
               handle_let_expr(vars, exprs, eb, st)
            } else if let Some((ef, ex)) = matches_apply_expr(list) {
               let next_kaddr = eval_alloc(st, 0);
               let next_k = Kont::ApplyList(None, ex, env.clone(), kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(EvalState::new(ef, env, store, next_kstore, next_kaddr))
            } else if let Some((prim, args)) = matches_prim_expr(list) {
               handle_prim_expr(prim, args, st)
            } else if let Some((prim, listexpr)) = matches_apply_prim_expr(list) {
               let next_kaddr = eval_alloc(st, 0);
               let next_k = Kont::ApplyPrim(prim, kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(EvalState::new(
                  listexpr,
                  env,
                  store,
                  next_kstore,
                  next_kaddr,
               ))
            } else if let Some(e) = matches_callcc_expr(list) {
               let next_kaddr = eval_alloc(st, 0);
               let next_k = Kont::Callcc(kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(EvalState::new(e, env, store, next_kstore, next_kaddr))
            } else if let Some((var, e)) = matches_setbang_expr(list) {
               let next_kaddr = eval_alloc(st, 0);
               let next_k = Kont::Set(env.get(&var).expect("no var"), kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(EvalState::new(e, env, store, next_kstore, next_kaddr))
            } else {
               handle_function_application_expr(list, st)
            }
         }
         Expr::Atom(_) => {
            panic!("Was not handled by atomic case??");
         }
      }
   }
}

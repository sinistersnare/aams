//!
//! Items to do with 'eval states'
//! Those are states that deal with evaluating the control
//! to reach a value.

use crate::common::{
   apply_state, eval_state, kalloc, Closure, ConcreteVal, EvalState, Expr, Kont, Prim, State, Val,
   Var,
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
         if let Some((argtype, body)) = matches_lambda_expr(list) {
            Val::new(ConcreteVal::Closure(Closure(argtype, body, env.clone())))
         } else if let Some(e) = matches_quote_expr(list) {
            Val::new(ConcreteVal::Quote(e))
         } else {
            panic!("Not given an atomic value, given some list.");
         }
      }
      Expr::Atom(ref atom) => {
         if let Some(n) = matches_number(atom) {
            Val::new(ConcreteVal::Number(n))
         } else if let Some(b) = matches_boolean(atom) {
            Val::new(ConcreteVal::Boolean(b))
         } else {
            store.get(
               &env
                  .get(&Var(atom.clone()))
                  .unwrap_or_else(|| panic!("Atom not in env: {:?}", atom)),
            )
         }
      }
   }
}

fn handle_prim_expr(prim: Prim, mut args: Vec<Expr>, st: &EvalState) -> State {
   let EvalState {
      ctrl,
      env,
      store,
      kaddr,
      ..
   } = st.clone();
   if args.is_empty() {
      let val = apply_prim(prim, &Val::new(ConcreteVal::Null));
      apply_state(val, store, kaddr)
   } else {
      let arg0 = args.remove(0);
      let next_kaddr = kalloc(ctrl);
      let next_k = Kont::Prim(
         prim,
         Vec::with_capacity(args.len()),
         args,
         env.clone(),
         kaddr,
      );
      let next_store = store.insertk(next_kaddr.clone(), next_k);
      eval_state(arg0, env, next_store, next_kaddr)
   }
}

fn handle_let_expr(vars: Vec<Var>, mut exprs: Vec<Expr>, eb: Expr, st: &EvalState) -> State {
   let EvalState {
      ctrl,
      env,
      store,
      kaddr,
      ..
   } = st.clone();
   let len = vars.len();
   if len == 0 {
      // why would you write (let () eb) you heathen
      // because of you I have to cover this case
      eval_state(eb, env, store, kaddr)
   } else {
      let e0 = exprs.remove(0);
      let rest = exprs;
      let next_kaddr = kalloc(ctrl);
      let next_k = Kont::Let(vars, Vec::with_capacity(len), rest, eb, env.clone(), kaddr);
      let next_store = store.insertk(next_kaddr.clone(), next_k);
      eval_state(e0, env, next_store, next_kaddr)
   }
}

fn handle_function_application_expr(list: &[Expr], st: &EvalState) -> State {
   let EvalState {
      ctrl,
      env,
      store,
      kaddr,
      ..
   } = st.clone();
   let mut args = list.to_vec();
   let func = args.remove(0);

   let next_kaddr = kalloc(ctrl);
   let next_k = Kont::App(Vec::with_capacity(list.len()), args, env.clone(), kaddr);
   let next_store = store.insertk(next_kaddr.clone(), next_k);
   eval_state(func, env, next_store, next_kaddr)
}

pub fn eval_step(st: &EvalState) -> State {
   let EvalState {
      ctrl,
      store,
      env,
      kaddr,
      ..
   } = st.clone();
   if is_atomic(&ctrl) {
      apply_state(atomic_eval(st), store, kaddr)
   } else {
      match ctrl {
         Expr::List(ref list) => {
            if let Some((ec, et, ef)) = matches_if_expr(list) {
               let next_kaddr = kalloc(ctrl.clone());
               let next_k = Kont::If(et, ef, env.clone(), kaddr);
               let next_store = store.insertk(next_kaddr.clone(), next_k);
               eval_state(ec, env, next_store, next_kaddr)
            } else if let Some((vars, exprs, eb)) = matches_let_expr(list) {
               handle_let_expr(vars, exprs, eb, st)
            } else if let Some((ef, ex)) = matches_apply_expr(list) {
               let next_kaddr = kalloc(ctrl.clone());
               let next_k = Kont::ApplyList(None, ex, env.clone(), kaddr);
               let next_store = store.insertk(next_kaddr.clone(), next_k);
               eval_state(ef, env, next_store, next_kaddr)
            } else if let Some((prim, args)) = matches_prim_expr(list) {
               handle_prim_expr(prim, args, st)
            } else if let Some((prim, listexpr)) = matches_apply_prim_expr(list) {
               let next_kaddr = kalloc(ctrl.clone());
               let next_k = Kont::ApplyPrim(prim, kaddr);
               let next_store = store.insertk(next_kaddr.clone(), next_k);
               eval_state(listexpr, env, next_store, next_kaddr)
            } else if let Some(e) = matches_callcc_expr(list) {
               let next_kaddr = kalloc(ctrl.clone());
               let next_k = Kont::Callcc(kaddr);
               let next_store = store.insertk(next_kaddr.clone(), next_k);
               eval_state(e, env, next_store, next_kaddr)
            } else if let Some((var, e)) = matches_setbang_expr(list) {
               let next_kaddr = kalloc(ctrl.clone());
               let next_k = Kont::Set(env.get(&var).expect("no var"), kaddr);
               let next_store = store.insertk(next_kaddr.clone(), next_k);
               eval_state(e, env, next_store, next_kaddr)
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

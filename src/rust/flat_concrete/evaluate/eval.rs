//! Handles eval states, which evalutes syntax to form a value.

use crate::flat_concrete::common::{BAddr, Closure, EvalState, KAddr, Kont, Prim, State, Val, Var};
use crate::flat_concrete::evaluate::matching::*;
use crate::flat_concrete::prims::PRIMS;
use crate::Expr;

pub fn is_atomic(ctrl: &Expr) -> bool {
   match ctrl {
      Expr::List(ref list) => {
         matches!(matches_lambda_expr(list), Some(_)) || matches!(matches_quote_expr(list), Some(_))
      }
      Expr::Atom(_) => true,
   }
}

pub fn atomic_eval(
   EvalState {
      ctrl, env, store, ..
   }: &EvalState,
) -> Val {
   match ctrl {
      Expr::List(ref list) => {
         if let Some((argtype, body)) = matches_lambda_expr(list) {
            Val::Closure(Closure(argtype, body, env.clone()))
         } else if let Some(e) = matches_quote_expr(list) {
            Val::Quote(e)
         } else {
            panic!("Not given an atomic value, given some list: {:?}", list);
         }
      }
      Expr::Atom(ref atom) => {
         if let Some(n) = matches_number(atom) {
            Val::Number(n)
         } else if let Some(b) = matches_boolean(atom) {
            Val::Boolean(b)
         } else {
            let addr = BAddr(Var(atom.clone()), env.clone());
            if store.contains_binding(&addr) {
               store.get(&addr)
            } else if PRIMS.contains_key(&**atom) {
               Val::Prim(Prim(atom.clone()))
            } else {
               panic!("unbound identifier: `{:?}`", atom);
            }
         }
      }
   }
}

pub fn eval_step(st: &EvalState) -> State {
   let EvalState {
      ctrl,
      env,
      store,
      kaddr,
   } = st.clone();
   if is_atomic(&ctrl) {
      State::apply(atomic_eval(&st), env, store, kaddr)
   } else {
      match ctrl {
         Expr::List(ref list) => {
            if let Some((ec, et, ef)) = matches_if_expr(list) {
               let next_kaddr = KAddr(store.count());
               let kont = Kont::If(et, ef, env.clone(), kaddr);
               let next_store = store.joink(next_kaddr.clone(), kont);
               State::eval(ec, env, next_store, next_kaddr)
            } else if let Some((vars, mut exprs, eb)) = matches_let_expr(list) {
               // God forgive me for I have sinned
               let lamexpr = Expr::List(vec![
                  Expr::Atom("lambda".to_string()),
                  Expr::List(vars.into_iter().map(|Var(v)| Expr::Atom(v)).collect()),
                  eb,
               ]);
               exprs.insert(0, lamexpr);
               State::eval(Expr::List(exprs), env, store, kaddr)
            } else if let Some((var, expr)) = matches_setbang_expr(list) {
               let addr = BAddr(var, env.clone());
               let next_kaddr = KAddr(store.count());
               let kont = Kont::Set(addr, kaddr);
               let next_store = store.joink(next_kaddr.clone(), kont);
               State::eval(expr, env, next_store, next_kaddr)
            } else if let Some(expr) = matches_callcc_expr(list) {
               let next_kaddr = KAddr(store.count());
               let kont = Kont::Callcc(ctrl, kaddr);
               let next_store = store.joink(next_kaddr.clone(), kont);
               State::eval(expr, env, next_store, next_kaddr)
            } else if let Some((ef, ea)) = matches_apply_expr(list) {
               let next_kaddr = KAddr(store.count());
               let kont = Kont::Apply(ctrl, None, ea, env.clone(), kaddr);
               let next_store = store.joink(next_kaddr.clone(), kont);
               State::eval(ef, env, next_store, next_kaddr)
            } else {
               // untagged function call
               let mut args = list.to_vec();
               let func = args.remove(0);
               let next_kaddr = KAddr(store.count());
               let kont = Kont::Call(
                  ctrl.clone(),
                  Vec::with_capacity(list.len()),
                  args,
                  env.clone(),
                  kaddr,
               );
               let next_store = store.joink(next_kaddr.clone(), kont);
               State::eval(func, env, next_store, next_kaddr)
            }
         }
         Expr::Atom(a) => {
            panic!("received an atom not handled in atomic case! `{:?}`", a);
         }
      }
   }
}

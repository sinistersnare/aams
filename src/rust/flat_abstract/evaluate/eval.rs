//! Handles eval states, which evalutes syntax to form a value.
//!
//! To alter this file for use in the abstract AM, I only had to:
//! * alter atomic_eval to return abstract values
//! * Use new abstract-KAddr allocation scheme

use crate::common::{Expr, Prim, Var};
use crate::matching::{Matching, match_syntax};
use crate::flat_abstract::domains::{BAddr, Closure, EvalState, InnerVal, KAddr, Kont, State, Val};
use crate::flat_abstract::prims::PRIMS;

pub fn atomic_eval(
   matching: Matching,
   EvalState {
      ctrl, env, store, ..
   }: &EvalState,
) -> Val {
   match matching {
      Matching::Quote(e) => {
         Val::from(InnerVal::Quote(e))
      }
      Matching::Number(n) => {
         Val::from(InnerVal::Number(n))
      }
      Matching::Boolean(b) => {
         Val::from(InnerVal::Boolean(b))
      }
      Matching::Lambda(argtype, body) => {
         Val::from_clo(Closure(argtype, body, env.clone()))
      }
      Matching::StrAtom(atom) => {
         let addr = BAddr(Var(atom.clone()), env.clone());
         if store.contains_binding(&addr) {
            store.get(&addr)
         } else if PRIMS.contains_key(&*atom) {
            Val::from(InnerVal::Prim(Prim(atom.clone())))
         } else {
            panic!("unbound identifier: `{:?}`", atom);
         }
      }
      complex_match => {
         panic!("Given a complex expression! {:?}", complex_match);
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
   match match_syntax(ctrl) {
      Matching::If(ec, et, ef) => {
         let next_kaddr = KAddr(ec.clone(), env.clone());
         let kont = Kont::If(et, ef, env.clone(), kaddr);
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(ec, env, next_store, next_kaddr)
      }
      Matching::Let(vars, exprs, eb) => {
         // God forgive me for I have sinned
         let lamexpr = Expr::List(vec![
            Expr::Atom("lambda".to_string()),
            Expr::List(vars.into_iter().map(|Var(v)| Expr::Atom(v)).collect()),
            eb,
         ]);
         exprs.insert(0, lamexpr);
         State::eval(Expr::List(exprs), env, store, kaddr)
      }
      Matching::SetBang(var, expr) => {
         let addr = BAddr(var, env.clone());
         let next_kaddr = KAddr(expr.clone(), env.clone());
         let kont = Kont::Set(addr, kaddr);
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(expr, env, next_store, next_kaddr)
      }
      Matching::Callcc(expr) => {
         let next_kaddr = KAddr(expr.clone(), env.clone());
         let kont = Kont::Callcc(ctrl, kaddr);
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(expr, env, next_store, next_kaddr)
      }
      Matching::Apply(ef, ea) => {
         let next_kaddr = KAddr(ef.clone(), env.clone());
         let kont = Kont::Apply(ctrl, None, ea, env.clone(), kaddr);
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(ef, env, next_store, next_kaddr)
      }
      Matching::Call(mut args) => {
         let func = args.remove(0);
         let next_kaddr = KAddr(func.clone(), env.clone());
         let kont = Kont::Call(
            ctrl.clone(),
            Vec::with_capacity(args.len() + 1),
            args,
            env.clone(),
            kaddr,
         );
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(func, env, next_store, next_kaddr)
      }
      atomic_match => {
         let val = atomic_eval(atomic_match, &st);
         State::apply(val, env, store, kaddr)
      }
   }
}

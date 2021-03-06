//! Handles eval states, which evalutes syntax to form a value.

use crate::common::{Expr, Prim, Var};
use crate::flat_concrete::domains::{Closure, BAddr, EvalState, KAddr, Kont, State, Val};
use crate::matching::{Matching, match_syntax};
use crate::flat_concrete::prims::PRIMS;

pub fn atomic_eval(
   matching: Matching,
   EvalState {
      env, store, ..
   }: &EvalState,
) -> Val {
   match matching {
      Matching::Lambda(argtype, body) => {
         Val::Closure(Closure(argtype, body, env.clone()))
      }
      Matching::Quote(e) => {
         Val::Quote(e)
      }
      Matching::StrAtom(atom) => {
         let addr = BAddr(Var(atom.clone()), env.clone());
         if store.contains_binding(&addr) {
            store.get(&addr)
         } else if PRIMS.contains_key(&*atom) {
            Val::Prim(Prim(atom))
         } else {
            panic!("unbound identifier: `{:?}`", atom);
         }
      }
      Matching::Boolean(b) => {
         Val::Boolean(b)
      }
      Matching::Number(n) => {
         Val::Number(n)
      }
      other => { panic!("`{:?}` is not atomic!", other);}
   }
}

pub fn eval_step(st: &EvalState) -> State {
   let EvalState {
      ctrl,
      env,
      store,
      kaddr,
   } = st.clone();
   match match_syntax(ctrl.clone()) {
      Matching::If(ec, et, ef) => {
         let next_kaddr = KAddr(store.count());
         let kont = Kont::If(et, ef, env.clone(), kaddr);
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(ec, env, next_store, next_kaddr)
      }
      Matching::Let(vars, mut exprs, eb) => {
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
         let next_kaddr = KAddr(store.count());
         let kont = Kont::Set(addr, kaddr);
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(expr, env, next_store, next_kaddr)
      }
      Matching::Callcc(expr) => {
         let next_kaddr = KAddr(store.count());
         let kont = Kont::Callcc(ctrl, kaddr);
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(expr, env, next_store, next_kaddr)
      }
      Matching::Apply(ef, ea) => {
         let next_kaddr = KAddr(store.count());
         let kont = Kont::Apply(ctrl, None, ea, env.clone(), kaddr);
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(ef, env, next_store, next_kaddr)
      }
      Matching::Call(mut args) => {
         let func = args.remove(0);
         let next_kaddr = KAddr(store.count());
         let kont = Kont::Call(
            ctrl,
            Vec::with_capacity(args.len() + 1),
            args,
            env.clone(),
            kaddr,
         );
         let next_store = store.joink(next_kaddr.clone(), kont);
         State::eval(func, env, next_store, next_kaddr)
      }
      other_match => {
         let val = atomic_eval(other_match, &st);
         State::apply(val, env, store, kaddr)
      }
   }
}

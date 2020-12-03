//!
//! Items to do with 'eval states'
//! Those are states that deal with applying syntax
//! To create a new state.

use crate::common::{
   Alloc, CloType, Closure, Kont, Prim, SExpr, SExprState, State, Val, ValState, Var,
};

use crate::common::{matches_boolean, matches_number};
use crate::prims::apply_prim;

fn is_atomic(ctrl: &SExpr) -> bool {
   match ctrl {
      SExpr::List(ref list) => {
         matches!(matches_lambda_expr(list), Some(_)) || matches!(matches_quote_expr(list), Some(_))
      }
      SExpr::Atom(_) => true,
   }
}

fn atomic_eval(
   SExprState {
      ctrl, env, store, ..
   }: &SExprState,
) -> Val {
   match ctrl {
      SExpr::List(ref list) => {
         if let Some((args, body)) = matches_lambda_expr(list) {
            Val::Closure(Closure(args, body, env.clone()))
         } else if let Some(e) = matches_quote_expr(list) {
            Val::Quote(e)
         } else {
            panic!("Not given an atomic value, given some list.");
         }
      }
      SExpr::Atom(ref atom) => {
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

fn handle_prim_expr(prim: Prim, mut args: Vec<SExpr>, st: &SExprState) -> State {
   let SExprState {
      env,
      store,
      kstore,
      kaddr,
      time,
      ..
   } = st.clone();
   if args.is_empty() {
      let val = apply_prim(prim, &[]);
      State::Apply(ValState::new(val, store, kstore, kaddr, time))
   } else {
      let arg0 = args.remove(0);
      let next_kaddr = st.alloc(0);
      let next_time = st.tick(1);
      let next_k = Kont::Prim(
         prim,
         Vec::with_capacity(args.len()),
         args,
         env.clone(),
         kaddr,
      );
      let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
      State::Eval(SExprState::new(
         arg0,
         env,
         store,
         next_kstore,
         next_kaddr,
         next_time,
      ))
   }
}

fn handle_let_expr(vars: Vec<Var>, mut exprs: Vec<SExpr>, eb: SExpr, st: &SExprState) -> State {
   let SExprState {
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
      State::Eval(SExprState::new(eb, env, store, kstore, kaddr, st.tick(1)))
   } else {
      let e0 = exprs.remove(0);
      let rest = exprs;
      let next_kaddr = st.alloc(0);
      let next_time = st.tick(1);
      let next_k = Kont::Let(vars, Vec::with_capacity(len), rest, eb, env.clone(), kaddr);
      let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
      State::Eval(SExprState::new(
         e0,
         env,
         store,
         next_kstore,
         next_kaddr,
         next_time,
      ))
   }
}

fn handle_function_application_expr(list: &[SExpr], st: &SExprState) -> State {
   let SExprState {
      env,
      store,
      kstore,
      kaddr,
      ..
   } = st.clone();
   let mut args = list.to_vec();
   let func = args.remove(0);

   let next_kaddr = st.alloc(0);
   let next_time = st.tick(1);
   let next_k = Kont::App(Vec::with_capacity(list.len()), args, env.clone(), kaddr);
   let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
   State::Eval(SExprState::new(
      func,
      env,
      store,
      next_kstore,
      next_kaddr,
      next_time,
   ))
}

pub fn eval_step(st: &SExprState) -> State {
   let SExprState {
      ctrl,
      store,
      kstore,
      env,
      kaddr,
      ..
   } = st.clone();
   if is_atomic(&ctrl) {
      let val = atomic_eval(st);
      State::Apply(ValState::new(val, store, kstore, kaddr, st.tick(1)))
   } else {
      match ctrl {
         SExpr::List(ref list) => {
            if let Some((ec, et, ef)) = matches_if_expr(list) {
               let next_kaddr = st.alloc(0);
               let next_time = st.tick(1);
               let next_k = Kont::If(et, ef, env.clone(), kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(SExprState::new(
                  ec,
                  env,
                  store,
                  next_kstore,
                  next_kaddr,
                  next_time,
               ))
            } else if let Some((vars, exprs, eb)) = matches_let_expr(list) {
               handle_let_expr(vars, exprs, eb, st)
            } else if let Some((ef, ex)) = matches_apply_expr(list) {
               let next_kaddr = st.alloc(0);
               let next_time = st.tick(1);
               let next_k = Kont::ApplyList(None, ex, env.clone(), kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(SExprState::new(
                  ef,
                  env,
                  store,
                  next_kstore,
                  next_kaddr,
                  next_time,
               ))
            } else if let Some((prim, args)) = matches_prim_expr(list) {
               handle_prim_expr(prim, args, st)
            } else if let Some((prim, listexpr)) = matches_apply_prim_expr(list) {
               let next_kaddr = st.alloc(0);
               let next_time = st.tick(1);
               let next_k = Kont::ApplyPrim(prim, kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(SExprState::new(
                  listexpr,
                  env,
                  store,
                  next_kstore,
                  next_kaddr,
                  next_time,
               ))
            } else if let Some(e) = matches_callcc_expr(list) {
               let next_kaddr = st.alloc(0);
               let next_time = st.tick(1);
               let next_k = Kont::Callcc(kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(SExprState::new(
                  e,
                  env,
                  store,
                  next_kstore,
                  next_kaddr,
                  next_time,
               ))
            } else if let Some((var, e)) = matches_setbang_expr(list) {
               let next_kaddr = st.alloc(0);
               let next_time = st.tick(1);
               let next_k = Kont::Set(env.get(&var).expect("no var"), kaddr);
               let next_kstore = kstore.insert(next_kaddr.clone(), next_k);
               State::Eval(SExprState::new(
                  e,
                  env,
                  store,
                  next_kstore,
                  next_kaddr,
                  next_time,
               ))
            } else {
               handle_function_application_expr(list, st)
            }
         }
         SExpr::Atom(_) => {
            panic!("Was not handled by atomic case??");
         }
      }
   }
}

////////////////////////////////////////
/////// Expression Matching Code ///////
////////////////////////////////////////

fn matches_quote_expr(list: &[SExpr]) -> Option<SExpr> {
   if list.len() == 2 && list[0] == SExpr::Atom("quote".to_string()) {
      Some(list[1].clone())
   } else {
      None
   }
}

fn matches_apply_expr(list: &[SExpr]) -> Option<(SExpr, SExpr)> {
   if list.len() == 3 && list[0] == SExpr::Atom("apply".to_string()) {
      Some((list[1].clone(), list[2].clone()))
   } else {
      None
   }
}

fn matches_lambda_expr(list: &[SExpr]) -> Option<(CloType, SExpr)> {
   if list.len() == 3
      && (list[0] == SExpr::Atom("lambda".to_string()) || list[0] == SExpr::Atom("λ".to_string()))
   {
      match list[1] {
         SExpr::List(ref args) => {
            let mut argvec = Vec::with_capacity(args.len());
            for arg_sexpr in args {
               match arg_sexpr {
                  SExpr::List(_) => {
                     panic!("Unexpected list in argument position");
                  }
                  SExpr::Atom(ref arg) => {
                     argvec.push(Var(arg.clone()));
                  }
               };
            }
            Some((CloType::MultiArg(argvec), list[2].clone()))
         }
         SExpr::Atom(ref var) => Some((CloType::VarArg(Var(var.clone())), list[2].clone())),
      }
   } else {
      None
   }
}

fn matches_if_expr(list: &[SExpr]) -> Option<(SExpr, SExpr, SExpr)> {
   if list.len() == 4 && list[0] == SExpr::Atom("if".to_string()) {
      Some((list[1].clone(), list[2].clone(), list[3].clone()))
   } else {
      None
   }
}

fn matches_let_expr(list: &[SExpr]) -> Option<(Vec<Var>, Vec<SExpr>, SExpr)> {
   if list.len() == 3 && list[0] == SExpr::Atom("let".to_string()) {
      match list[1] {
         SExpr::List(ref outer) => {
            let mut vars = Vec::with_capacity(outer.len());
            let mut exprs = Vec::with_capacity(outer.len());
            for binding in outer {
               match binding {
                  SExpr::List(ref entry) => {
                     if entry.len() != 2 {
                        panic!("Let entry must only have 2 elements.");
                     }
                     match entry[0] {
                        SExpr::List(_) => {
                           panic!("Binding name must be an atom.");
                        }
                        SExpr::Atom(ref v) => {
                           vars.push(Var(v.clone()));
                           exprs.push(entry[1].clone());
                        }
                     }
                  }
                  SExpr::Atom(_) => {
                     panic!("Bindings are len-2 lists, not atoms.");
                  }
               }
            }
            Some((vars, exprs, list[2].clone()))
         }
         SExpr::Atom(_) => {
            panic!("Let takes a binding list, not a single arg");
         }
      }
   } else {
      None
   }
}

fn matches_prim_expr(list: &[SExpr]) -> Option<(Prim, Vec<SExpr>)> {
   if list.len() >= 2 && list[0] == SExpr::Atom("prim".to_string()) {
      let primname = match list[1] {
         SExpr::List(_) => {
            panic!("Unexpected list in prim-name position");
         }
         SExpr::Atom(ref name) => name.clone(),
      };
      Some((Prim(primname), list[2..].to_vec()))
   } else {
      None
   }
}

fn matches_apply_prim_expr(list: &[SExpr]) -> Option<(Prim, SExpr)> {
   if list.len() == 3 && list[0] == SExpr::Atom("apply-prim".to_string()) {
      let primname = match list[1] {
         SExpr::List(_) => {
            panic!("Unexpected list in prim-name position");
         }
         SExpr::Atom(ref name) => name.clone(),
      };
      let arglist = list[2].clone();
      Some((Prim(primname), arglist))
   } else {
      None
   }
}

fn matches_callcc_expr(list: &[SExpr]) -> Option<SExpr> {
   if list.len() == 2 && list[0] == SExpr::Atom("call/cc".to_string()) {
      Some(list[1].clone())
   } else {
      None
   }
}

fn matches_setbang_expr(list: &[SExpr]) -> Option<(Var, SExpr)> {
   if list.len() == 3 && list[0] == SExpr::Atom("set!".to_string()) {
      match list[1] {
         SExpr::Atom(ref x) => Some((Var(x.clone()), list[2].clone())),
         SExpr::List(_) => {
            panic!("set! takes a var then an expression");
         }
      }
   } else {
      None
   }
}

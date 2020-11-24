//!
//! Items to do with 'eval states'
//! Those are states that deal with applying syntax
//! To create a new state.

use crate::common::{
   Alloc, CloType, Closure, Kont, Prim, SExpr, SExprState, State, Store, Val, ValState, Var,
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

fn atomic_eval(SExprState { ctrl, env, .. }: &SExprState, store: &Store) -> Val {
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
               .get(env.get(Var(atom.clone())).expect("Atom not in env"))
               .expect("Atom not in store")
         }
      }
   }
}

fn handle_prim_expr(prim: Prim, mut args: Vec<SExpr>, st: &SExprState, store: &mut Store) -> State {
   let SExprState { env, kont_addr, .. } = st.clone();
   if args.is_empty() {
      let val = apply_prim(prim, &[]);
      State::Apply(ValState::new(val, env, kont_addr, st.tick(1)))
   } else {
      let arg0 = args.remove(0);
      let new_kont = Kont::Prim(
         prim,
         Vec::with_capacity(args.len()),
         args,
         env.clone(),
         kont_addr,
      );
      let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
      State::Eval(SExprState::new(arg0, env, next_kaddr, st.tick(1)))
   }
}

fn handle_let_expr(
   vars: Vec<Var>,
   mut exprs: Vec<SExpr>,
   eb: SExpr,
   st: &SExprState,
   store: &mut Store,
) -> State {
   let SExprState { env, kont_addr, .. } = st.clone();
   let len = vars.len();
   if len == 0 {
      // why would you write (let () eb) you heathen
      // because of you I have to cover this case
      State::Eval(SExprState::new(eb, env, kont_addr, st.tick(1)))
   } else {
      let e0 = exprs.remove(0);
      let rest = exprs;
      let new_kont = Kont::Let(
         vars,
         Vec::with_capacity(len),
         rest,
         eb,
         env.clone(),
         kont_addr,
      );
      let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
      State::Eval(SExprState::new(e0, env, next_kaddr, st.tick(1)))
   }
}

fn handle_function_application_expr(list: &[SExpr], st: &SExprState, store: &mut Store) -> State {
   let SExprState { env, kont_addr, .. } = st.clone();
   // application case
   let (func, args) = list.split_first().expect("Given Empty List");
   let new_kont = Kont::App(
      Vec::with_capacity(list.len()),
      args.to_vec(),
      env.clone(),
      kont_addr,
   );
   let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
   State::Eval(SExprState::new(func.clone(), env, next_kaddr, st.tick(1)))
}

pub fn eval_step(st: &SExprState, store: &mut Store) -> State {
   let SExprState {
      ctrl,
      env,
      kont_addr,
      ..
   } = st.clone();
   if is_atomic(&ctrl) {
      let val = atomic_eval(st, store);
      let val_state = ValState::new(val, env, kont_addr, st.tick(1));
      State::Apply(val_state)
   } else {
      match ctrl {
         SExpr::List(ref list) => {
            if let Some((ec, et, ef)) = matches_if_expr(list) {
               let new_kont = Kont::If(et, ef, env.clone(), kont_addr);
               let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
               State::Eval(SExprState::new(ec, env, next_kaddr, st.tick(1)))
            } else if let Some((vars, exprs, eb)) = matches_let_expr(list) {
               handle_let_expr(vars, exprs, eb, st, store)
            } else if let Some((func, arglist)) = matches_apply_expr(list) {
               let new_kont = Kont::ApplyList(None, arglist, env.clone(), kont_addr);
               let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
               State::Eval(SExprState::new(func, env, next_kaddr, st.tick(1)))
            } else if let Some((prim, args)) = matches_prim_expr(list) {
               handle_prim_expr(prim, args, st, store)
            } else if let Some((prim, listexpr)) = matches_apply_prim_expr(list) {
               let new_kont = Kont::ApplyPrim(prim, env.clone(), kont_addr);
               let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
               State::Eval(SExprState::new(listexpr, env, next_kaddr, st.tick(1)))
            } else if let Some(e) = matches_callcc_expr(list) {
               let new_kont = Kont::Callcc(env.clone(), kont_addr);
               let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
               State::Eval(SExprState::new(e, env, next_kaddr, st.tick(1)))
            } else if let Some((var, e)) = matches_setbang_expr(list) {
               let new_kont = Kont::Set(var, env.clone(), kont_addr);
               let next_kaddr = store.add_to_store(Val::Kont(new_kont), st);
               State::Eval(SExprState::new(e, env, next_kaddr, st.tick(1)))
            } else {
               handle_function_application_expr(list, st, store)
            }
         }
         SExpr::Atom(ref _atom) => {
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

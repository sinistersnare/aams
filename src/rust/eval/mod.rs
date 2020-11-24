//!
//! The evaluator of scheme ASTs.

pub mod apply;
pub mod eval;

use crate::common::{Addr, Env, Kont, SExpr, SExprState, State, Store, Time, Val};
use apply::apply_step;
use eval::eval_step;

fn inject(ctrl: SExpr) -> State {
   // Time 0 was for creation of the state, we start on 1.
   // (becuase mt is addr 0, we need to start with 1)
   State::Eval(SExprState::new(
      ctrl,
      Env(im::HashMap::new()),
      Addr(0),
      Time(1),
   ))
}

pub fn step(st: &State, store: &mut Store) -> State {
   match st {
      State::Eval(sexpr_state) => eval_step(sexpr_state, store),
      State::Apply(val_state) => apply_step(val_state, store),
   }
}

pub fn evaluate(ctrl: SExpr) -> (Vec<State>, Store) {
   // initially the store only has the Empty continuation
   let mut inner = std::collections::HashMap::new();
   inner.insert(Addr(0), Val::Kont(Kont::Empty));
   let mut store = Store(inner);

   let mut st0 = inject(ctrl);
   let mut stepped = step(&st0, &mut store);
   let mut states = vec![st0.clone(), stepped.clone()];
   while st0 != stepped {
      st0 = stepped;
      stepped = step(&st0, &mut store);
      states.push(stepped.clone());
   }
   (states, store)
}

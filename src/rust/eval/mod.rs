//!
//! The evaluator of scheme ASTs.

mod apply;
mod eval;

use crate::common::{Addr, Env, KStore, Kont, SExpr, SExprState, State, Store, Time};
use apply::apply_step;
use eval::eval_step;

fn inject(ctrl: SExpr) -> State {
   // Time 0 was for creation of the state, we start on 1.
   // (becuase mt is addr 0, we need to start with 1)
   State::Eval(SExprState::new(
      ctrl,
      Env(im::HashMap::new()),
      Store(im::HashMap::new()),
      KStore(im::HashMap::unit(Addr(0), Kont::Empty)),
      Addr(0),
      Time(1),
   ))
}

pub fn step(st: &State) -> State {
   match st {
      State::Eval(sexpr_state) => eval_step(sexpr_state),
      State::Apply(val_state) => apply_step(val_state),
   }
}

pub fn evaluate(ctrl: SExpr) -> Vec<State> {
   let mut st0 = inject(ctrl);
   let mut stepped = step(&st0);
   let mut states = vec![st0.clone(), stepped.clone()];
   while st0 != stepped {
      st0 = stepped;
      stepped = step(&st0);
      states.push(stepped.clone());
   }
   states
}

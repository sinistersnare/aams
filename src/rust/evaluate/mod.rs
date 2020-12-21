//!
//! The evaluator of scheme ASTs.

mod apply;
mod eval;
pub mod matching;

use crate::common::{Addr, Env, EvalState, Expr, KStore, Kont, State, Store, Time};
use apply::apply_step;
use eval::eval_step;

fn inject(ctrl: Expr) -> State {
   // Time 0 was for creation of the state, we start on 1.
   // (becuase mt is addr 0, we need to start with 1)
   State::Eval(EvalState::new(
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
      State::Eval(eval_state) => eval_step(eval_state),
      State::Apply(apply_state) => apply_step(apply_state),
   }
}

pub fn evaluate(ctrl: Expr) -> Vec<State> {
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

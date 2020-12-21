//!
//! The evaluator of scheme ASTs.

mod apply;
mod eval;
pub mod matching;

use crate::common::{eval_state, Address, Env, Expr, Kont, State, Store};
use apply::apply_step;
use eval::eval_step;

fn inject(ctrl: Expr) -> State {
   eval_state(
      ctrl,
      Env(im::HashMap::new()),
      Store::new().insertk(Address::KAddr(Expr::Atom("".to_string()), 0), Kont::Empty),
      Address::KAddr(Expr::Atom("".to_string()), 0),
   )
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

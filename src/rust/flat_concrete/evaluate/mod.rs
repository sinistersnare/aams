//!
//! The evaluator of scheme ASTs.

mod apply;
mod eval;
mod matching;

use crate::flat_concrete::common::{Env, KAddr, Kont, State, Store};
use crate::Expr;
use apply::apply_step;
use eval::eval_step;

fn inject(ctrl: Expr) -> State {
   let addr0 = KAddr(0);
   State::eval(
      ctrl,
      Env::new(),
      Store::new().joink(addr0.clone(), Kont::Empty),
      addr0,
   )
}

fn step(st: &State) -> State {
   match st {
      State::E(eval_state) => eval_step(eval_state),
      State::A(apply_state) => apply_step(apply_state),
   }
}

pub fn evaluate(ctrl: Expr) -> Vec<State> {
   let s0 = inject(ctrl);
   let mut states = Vec::with_capacity(128);
   states.push(s0.clone());
   let mut cur = s0;
   loop {
      let next = step(&cur);
      if cur == next {
         break;
      }
      states.push(next.clone());
      cur = next;
   }
   states
}

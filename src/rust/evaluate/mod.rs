//!
//! The evaluator of scheme ASTs.

mod apply;
mod eval;
pub mod matching;

use crate::common::{eval_state, Address, Env, Expr, Kont, State, Store};
use apply::apply_step;
use eval::eval_step;

use std::iter::FromIterator;

fn inject(ctrl: Expr) -> State {
   eval_state(
      ctrl,
      Env(im::HashMap::new()),
      Store::new().insertk(Address::KAddr(Expr::Atom("".to_string())), Kont::Empty),
      Address::KAddr(Expr::Atom("".to_string())),
   )
}

pub fn step(st: &State) -> im::HashSet<State> {
   match st {
      State::Eval(eval_state) => im::HashSet::unit(eval_step(eval_state)),
      State::Apply(apply_state) => apply_step(apply_state),
   }
}

pub fn evaluate(ctrl: Expr) -> im::HashSet<State> {
   search(im::HashSet::new(), im::Vector::unit(inject(ctrl)))
}

fn search(seen: im::HashSet<State>, mut todo: im::Vector<State>) -> im::HashSet<State> {
   if todo.is_empty() {
      seen
   } else {
      let head = todo.remove(0);
      if seen.contains(&head) {
         search(seen, todo)
      } else {
         search(
            seen.update(head.clone()),
            im::Vector::from_iter(step(&head).into_iter()) + todo,
         )
      }
   }
}

//!
//! The evaluator of scheme ASTs.

mod apply;
mod eval;
pub mod matching;

use crate::common::{eval_state, kalloc, Env, Expr, Kont, State, Store};
use apply::apply_step;
use eval::eval_step;

use std::iter::FromIterator;

fn inject(ctrl: Expr) -> State {
   eval_state(
      ctrl,
      Env(im::HashMap::new()),
      Store::new().insertk(kalloc(Expr::Atom("".to_string())), Kont::Empty),
      kalloc(Expr::Atom("".to_string())),
   )
}

/// the transfer function
fn step(st: &State) -> im::HashSet<State> {
   match st {
      State::Eval(eval_state) => im::HashSet::unit(eval_step(eval_state)),
      State::Apply(apply_state) => apply_step(apply_state),
   }
}

/// takes an initial expression, and evaluates it into a set of reachable states.
pub fn evaluate(ctrl: Expr) -> im::HashMap<State, im::HashSet<State>> {
   let e0 = inject(ctrl);
   let mut cfg = im::HashMap::new();
   let mut todo = im::Vector::unit(e0);
   while !todo.is_empty() {
      let doing = todo.remove(0);
      // if we have already processed this state, dont do it again.
      if cfg.contains_key(&doing) {
         continue;
      }
      let results = step(&doing);

      let combined_stores = combine_stores(results);
      // add to CFG
      cfg = cfg.update(doing, combined_stores.clone());
      todo = im::Vector::from_iter(combined_stores.into_iter()) + todo;
   }
   cfg
}

// joins all the stores in the given states, to globalize the store component.
fn combine_stores(states: im::HashSet<State>) -> im::HashSet<State> {
   // first figure out what the combined, 'global', store is
   let global = states
      .clone()
      .into_iter()
      .fold(Store::new(), |accum, st| match st {
         State::Eval(e) => accum.join(e.store),
         State::Apply(a) => accum.join(a.store),
      });
   // then change every store out with the globalized one.
   states
      .into_iter()
      .map(|o| o.set_store(global.clone()))
      .collect()
}

//!
//! The evaluator of scheme ASTs.

mod apply;
mod eval;

use crate::common::Expr;
use crate::flat_abstract::domains::{Env, KAddr, Kont, State, Store};
use apply::apply_step;
use eval::eval_step;

fn inject(ctrl: Expr) -> State {
   let env0 = Env::new();
   let addr0 = KAddr(ctrl.clone(), env0.clone());
   State::eval(
      ctrl,
      env0,
      Store::new().joink(addr0.clone(), Kont::Empty),
      addr0,
   )
}

fn step(st: &State) -> im::HashSet<State> {
   match st {
      State::E(eval_state) => im::HashSet::unit(eval_step(eval_state)),
      State::A(apply_state) => apply_step(apply_state),
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
      todo = combined_stores.into_iter().collect::<im::Vector<_>>() + todo;
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
         State::E(e) => accum.combine(e.store),
         State::A(a) => accum.combine(a.store),
      });
   // then change every store out with the globalized one.
   states
      .into_iter()
      .map(|o| o.set_store(global.clone()))
      .collect()
}

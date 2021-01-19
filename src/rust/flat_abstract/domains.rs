//! Machine specific domains

use crate::common::{Expr, LambdaArgType, Var, Prim};

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum State {
   E(EvalState),
   A(ApplyState),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct EvalState {
   pub ctrl: Expr,
   pub env: Env,
   pub store: Store,
   pub kaddr: KAddr,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct ApplyState {
   pub val: Val,
   pub env: Env,
   pub store: Store,
   pub kaddr: KAddr,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Env(im::Vector<Expr>);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Store {
   bindings: im::HashMap<BAddr, Val>,
   kontinuations: im::HashMap<KAddr, im::HashSet<Kont>>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct BAddr(pub Var, pub Env);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct KAddr(pub Expr, pub Env);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Val {
   inner_val: Result<InnerVal, bool>,
   closures: im::HashSet<Closure>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum InnerVal {
   Null,
   Void,
   Prim(Prim),
   Number(i64),
   Kont(Kont),
   Boolean(bool),
   Quote(Expr),
   Cons(Box<Val>, Box<Val>),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Closure(pub LambdaArgType, pub Expr, pub Env);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum Kont {
   Empty,
   If(Expr, Expr, Env, KAddr),
   Set(BAddr, KAddr),
   Callcc(Expr, KAddr),
   Apply(Expr, Option<Box<Val>>, Expr, Env, KAddr),
   /// TODO: should these vecs (and others in common.rs) be im::Vector?
   Call(Expr, Vec<Val>, Vec<Expr>, Env, KAddr),
}

impl State {
   pub fn eval(ctrl: Expr, env: Env, store: Store, kaddr: KAddr) -> Self {
      State::E(EvalState {
         ctrl,
         env,
         store,
         kaddr,
      })
   }

   pub fn apply(val: Val, env: Env, store: Store, kaddr: KAddr) -> Self {
      State::A(ApplyState {
         val,
         env,
         store,
         kaddr,
      })
   }

   pub fn set_store(self, store: Store) -> Self {
      match self {
         State::E(EvalState { ctrl, env, kaddr, .. }) =>
            State::eval(ctrl, env, store, kaddr),
         State::A(ApplyState { val, env, kaddr, .. }) =>
            State::apply(val, env, store, kaddr),
      }
   }
}

impl Env {
   pub fn new() -> Self {
      Env(im::Vector::new())
   }

   pub fn next(&self, expr: Expr) -> Self {
      let mut next = self.0.clone();
      next.push_front(expr);
      let (left, _) = next.split_at(crate::flat_abstract::M);
      Env(left)
   }
}

impl Store {
   pub fn new() -> Self {
      Store {
         bindings: im::HashMap::new(),
         kontinuations: im::HashMap::new(),
      }
   }

   pub fn join(&self, baddr: BAddr, val: Val) -> Self {
      Store {
         bindings: self.bindings.update(baddr, val),
         kontinuations: self.kontinuations.clone(),
      }
   }

   pub fn joink(&self, kaddr: KAddr, kont: Kont) -> Self {
      let konts = if let Some(old) = self.kontinuations.get(&kaddr) {
         old.update(kont)
      } else {
         im::HashSet::unit(kont)
      };
      Store {
         bindings: self.bindings.clone(),
         kontinuations: self.kontinuations.update(kaddr, konts),
      }
   }

   pub fn get(&self, baddr: &BAddr) -> Val {
      self
         .bindings
         .get(baddr)
         .expect(&*format!("BAddr not found: {:?}", baddr))
         .clone()
   }

   pub fn getk(&self, kaddr: &KAddr) -> im::HashSet<Kont> {
      self
         .kontinuations
         .get(kaddr)
         .expect("KAddr not found")
         .clone()
   }

   pub fn contains_binding(&self, baddr: &BAddr) -> bool {
      self.bindings.contains_key(baddr)
   }

   // used to implement the single-threaded global store.
   pub fn combine(self, other: Self) -> Store {
      Store {
         bindings: self
            .bindings
            .union_with(other.bindings, |v1, v2| Val::from_old(Some(&v1), v2)),
         kontinuations: self
            .kontinuations
            .union_with(other.kontinuations, |v1, v2| v1.union(v2)),
      }
   }
}

impl Val {
   pub fn from(iv: InnerVal) -> Self {
      Val {
         inner_val: Ok(iv),
         closures: im::HashSet::new(),
      }
   }

   pub fn from_clo(c: Closure) -> Self {
      Val {
         inner_val: Err(false),
         closures: im::HashSet::unit(c),
      }
   }

   pub fn from_old(old: Option<&Self> , new: Self) -> Self {
      match old {
         None => new,
         Some(old) => Val {
            closures: old.closures.clone().union(new.closures),
            inner_val: match (old.inner_val , new.inner_val) {
               (Err(true), _) | (_ , Err(true)) => Err(true),
               (Err(false), other) | (other, Err(false)) => other,
               (Ok(v1), Ok(v2)) => {
                  if v1 == v2 {
                     Ok(v1)
                  } else {
                     Err(true)
                  }
               }
            }
         }
      }
   }

   pub fn top() -> Self {
      Val {
         inner_val: Err(true),
         closures: im::HashSet::new(),
      }
   }
}

//! Machine specific domains

use crate::common::{Expr, LambdaArgType, Prim, Var};

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
   pub inner_val: Result<InnerVal, bool>,
   pub primitives: im::HashSet<Prim>,
   pub kontinuations: im::HashSet<Kont>,
   pub closures: im::HashSet<Closure>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum InnerVal {
   Null,
   Void,
   Number(i64),
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
         State::E(EvalState {
            ctrl, env, kaddr, ..
         }) => State::eval(ctrl, env, store, kaddr),
         State::A(ApplyState {
            val, env, kaddr, ..
         }) => State::apply(val, env, store, kaddr),
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
         bindings: self
            .bindings
            .update(baddr.clone(), Val::from_old(self.bindings.get(&baddr), val)),
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
   /// creates an empty value,
   /// should only be used interally to form a correct Val.
   fn new() -> Self {
      Val {
         inner_val: Err(false),
         primitives: im::HashSet::new(),
         kontinuations: im::HashSet::new(),
         closures: im::HashSet::new(),
      }
   }

   pub fn from(iv: InnerVal) -> Self {
      let mut v = Val::new();
      v.inner_val = Ok(iv);
      v
   }

   pub fn from_prim(p: Prim) -> Self {
      let mut v = Val::new();
      v.primitives = im::HashSet::unit(p);
      v
   }

   pub fn from_kont(k: Kont) -> Self {
      let mut v = Val::new();
      v.kontinuations = im::HashSet::unit(k);
      v
   }

   pub fn from_clo(c: Closure) -> Self {
      let mut v = Val::new();
      v.closures = im::HashSet::unit(c);
      v
   }

   pub fn top() -> Self {
      let mut v = Val::new();
      v.inner_val = Err(true);
      v
   }

   pub fn from_old(old: Option<&Self>, new: Self) -> Self {
      match old {
         None => new,
         Some(old) => Val {
            kontinuations: old.kontinuations.clone().union(new.kontinuations),
            primitives: old.primitives.clone().union(new.primitives),
            closures: old.closures.clone().union(new.closures),
            inner_val: match (old.inner_val.clone(), new.inner_val) {
               (Err(true), _) | (_, Err(true)) => Err(true),
               (Err(false), other) | (other, Err(false)) => other,
               (Ok(v1), Ok(v2)) => {
                  if v1 == v2 {
                     Ok(v1)
                  } else {
                     Err(true)
                  }
               }
            },
         },
      }
   }

   pub fn is_truthy(&self) -> bool {
      match self.inner_val {
         Err(false) => true,
         Ok(ref iv) => iv != &InnerVal::Boolean(false),
         _ => false,
      }
   }

   pub fn is_falsy(&self) -> bool {
      self == &Val::from(InnerVal::Boolean(false))
   }

   // returns the number if this value is only ever a number.
   pub fn is_number(&self) -> Option<i64> {
      if self.primitives.is_empty() && self.kontinuations.is_empty() && self.closures.is_empty() {
         if let Ok(InnerVal::Number(n)) = self.inner_val {
            Some(n)
         } else {
            None
         }
      } else {
         None
      }
   }

   pub fn is_cons(&self) -> Option<(Box<Val>, Box<Val>)> {
      if self.primitives.is_empty() && self.kontinuations.is_empty() && self.closures.is_empty() {
         if let Ok(InnerVal::Cons(car, cdr)) = self.inner_val.clone() {
            Some((car, cdr))
         } else {
            None
         }
      } else {
         None
      }
   }
}

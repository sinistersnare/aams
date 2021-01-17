use crate::Expr;

//#[derive(Debug, Hash, Clone, PartialEq, Eq)]

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
pub struct Env(usize, im::Vector<Expr>);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Store {
   bindings: im::HashMap<BAddr, Val>,
   kontinuations: im::HashMap<KAddr, Kont>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct BAddr(pub Var, pub Env);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct KAddr(pub usize);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum Val {
   Null,
   Void,
   Prim(Prim),
   Closure(Closure),
   Number(i64),
   Kont(Kont),
   Boolean(bool),
   Quote(Expr),
   Cons(Box<Val>, Box<Val>),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Closure(pub LambdaArgType, pub Expr, pub Env);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum LambdaArgType {
   FixedArg(Vec<Var>),
   VarArg(Var),
}

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

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Var(pub String);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Prim(pub String);

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
}

impl Env {
   pub fn new() -> Self {
      Env(0, im::Vector::new())
   }

   pub fn next(&self, expr: Expr) -> Self {
      let mut next = self.1.clone();
      next.push_front(expr);
      Env(self.0 + 1, next)
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
      Store {
         bindings: self.bindings.clone(),
         kontinuations: self.kontinuations.update(kaddr, kont),
      }
   }

   pub fn get(&self, baddr: &BAddr) -> Val {
      self
         .bindings
         .get(baddr)
         .expect(&*format!("BAddr not found: {:?}", baddr))
         .clone()
   }

   pub fn getk(&self, kaddr: &KAddr) -> Kont {
      self
         .kontinuations
         .get(kaddr)
         .expect("KAddr not found")
         .clone()
   }

   pub fn count(&self) -> usize {
      self.bindings.len() + self.kontinuations.len()
   }

   pub fn contains_binding(&self, baddr: &BAddr) -> bool {
      self.bindings.contains_key(baddr)
   }
}

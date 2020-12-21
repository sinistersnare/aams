use std::fmt;

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum State {
   Eval(EvalState),
   Apply(ApplyState),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct EvalState {
   pub ctrl: Expr,
   pub env: Env,
   pub store: Store,
   pub kaddr: Address,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct ApplyState {
   pub val: Val,
   pub store: Store,
   pub kaddr: Address,
}

#[derive(Hash, Clone, PartialEq, Eq)]
pub enum Expr {
   List(Vec<Expr>),
   Atom(String),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Env(pub im::HashMap<Var, Address>);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Store {
   binds: im::HashMap<Address, Val>,
   konts: im::HashMap<Address, Kont>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum Val {
   /// Also can be used as end-of-list sentinel value.
   Null,
   /// returned by things like `(set! x e)`, (prim println), etc.
   Void,
   /// A closure is a syntactic lambda (a function) with an environment
   /// so that free variables inside of it are bound.
   Closure(Closure),
   /// A number... do you need docs?
   /// TODO: make f64.
   Number(i64),
   /// A reified continuation, which can be called with 1 argument
   /// to continue processing with the continuation.
   Kont(Kont),
   /// a boolean value, can be true or false.
   Boolean(bool),
   /// A quoted S-Expression, which does not evaluate it.
   Quote(Expr),
   /// a compound object formed from 2 other values
   /// can be used to implement lists.
   Cons(Box<Val>, Box<Val>),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Closure(pub CloType, pub Expr, pub Env);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum CloType {
   MultiArg(Vec<Var>),
   VarArg(Var),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum Kont {
   /// The empty continuation, meaning there is nothing else to do.
   Empty,
   /// a conditional
   If(Expr, Expr, Env, Address),
   /// A let binding continuation
   /// After each Expr in
   Let(Vec<Var>, Vec<Val>, Vec<Expr>, Expr, Env, Address),
   Callcc(Address),
   Set(Address, Address),
   Prim(Prim, Vec<Val>, Vec<Expr>, Env, Address),
   ApplyPrim(Prim, Address),
   ApplyList(Option<Box<Val>>, Expr, Env, Address),
   App(Vec<Val>, Vec<Expr>, Env, Address),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Var(pub String);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Address {
   // which variable we are binding
   BAddr(Var, usize),
   KAddr(Expr, usize),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Prim(pub String);

impl EvalState {
   pub fn new(ctrl: Expr, env: Env, store: Store, kaddr: Address) -> EvalState {
      EvalState {
         ctrl,
         env,
         store,
         kaddr,
      }
   }
}

impl ApplyState {
   pub fn new(val: Val, store: Store, kaddr: Address) -> ApplyState {
      ApplyState { val, store, kaddr }
   }
}

impl Env {
   pub fn insert(&self, k: Var, v: Address) -> Env {
      let mut newenv = self.0.clone();
      newenv.insert(k, v);
      Env(newenv)
   }

   pub fn get(&self, var: &Var) -> Option<Address> {
      self.0.get(var).cloned()
   }
}

impl Store {
   pub fn new() -> Store {
      Store {
         binds: im::HashMap::new(),
         konts: im::HashMap::new(),
      }
   }

   pub fn insert(&self, k: Address, v: Val) -> Store {
      if let Address::BAddr(..) = k {
         Store {
            binds: self.binds.update(k, v),
            konts: self.konts.clone(),
         }
      } else {
         panic!("Not given a binding-addr with the value. {:?}", k);
      }
   }

   pub fn insertk(&self, a: Address, k: Kont) -> Store {
      if let Address::KAddr(..) = a {
         Store {
            binds: self.binds.clone(),
            konts: self.konts.update(a, k),
         }
      } else {
         panic!("Not given a kont-addr with the kont. {:?}", k);
      }
   }

   pub fn get(&self, k: &Address) -> Option<Val> {
      match k {
         Address::BAddr(..) => self.binds.get(k).cloned(),
         Address::KAddr(..) => self.konts.get(k).cloned().map(|k| Val::Kont(k)),
      }
   }
}

impl fmt::Debug for Expr {
   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      match self {
         Expr::List(ref list) => {
            write!(f, "(")?;
            for (i, e) in list.iter().enumerate() {
               write!(f, "{:?}", e)?;
               if i + 1 != list.len() {
                  write!(f, " ")?;
               }
            }
            write!(f, ")")
         }
         Expr::Atom(ref atom) => write!(f, "{}", atom),
      }
   }
}

pub fn val_is_list(val: &Val) -> bool {
   if !matches!(val, Val::Cons(_, _)|Val::Null) {
      return false;
   }
   let mut cur = val;
   while let Val::Cons(_, cdr) = cur {
      cur = &*cdr;
   }
   matches!(cur, Val::Null)
}

pub fn make_scm_list(vals: Vec<Val>) -> Val {
   let mut lst = Val::Null;
   for v in vals.into_iter().rev() {
      lst = Val::Cons(Box::new(v), Box::new(lst));
   }
   lst
}

pub fn scm_list_to_vals(val: Val) -> Vec<Val> {
   let mut vals = vec![];
   let mut cur = val;
   while let Val::Cons(car, cdr) = cur {
      vals.push(*car);
      cur = *cdr;
   }
   vals
}

pub fn matches_number(str: &str) -> Option<i64> {
   str.parse::<i64>().ok()
}

pub fn matches_boolean(str: &str) -> Option<bool> {
   // because we cant parse #t/#f rn, just use true/false.
   if str == "#t" {
      Some(true)
   } else if str == "#f" {
      Some(false)
   } else {
      None
   }
}

/// Allocates an address for a binding
/// TODO: actually write these...
pub fn apply_alloc(_st: &ApplyState, _offset: usize) -> Address {
   Address::BAddr(Var("WRONG".to_string()), 0)
}

/// Allocates an address for a continuation
pub fn eval_alloc(_st: &EvalState, _offset: usize) -> Address {
   Address::BAddr(Var("WRONG".to_string()), 0)
}

pub fn apply_state(val: Val, store: Store, kaddr: Address) -> State {
   State::Apply(ApplyState::new(val, store, kaddr))
}

pub fn eval_state(ctrl: Expr, env: Env, store: Store, kaddr: Address) -> State {
   State::Eval(EvalState::new(ctrl, env, store, kaddr))
}

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
   konts: im::HashMap<Address, im::HashSet<Kont>>,
}

// The way we are doing abstraction of the store is as so
// the store is Addr -> Val
// val is the lattice, and we define the `join` operator
// to update the val if it exists already.

/// An abstract value (cause this is an AAM)
/// An abstract value is a lattice that can hold a single concrete-value, or be top.
/// Also, it has a set of closures that it can be.
#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Val {
   /// If there is only a single possible val for this, then it is Ok,
   /// If multiple values are given, its Err(true) for top.
   /// If no values are given (only ever closures) this is Err(false) for bottom.
   pub vals: Result<ConcreteVal, bool>,
   /// The set of closures that that can inhabit this value.
   pub closures: im::HashSet<Closure>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum ConcreteVal {
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
   /// a compound object formed from 2 values
   /// can be used to implement lists.
   /// (note how these are abstract values not concrete)
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
   /// which variable we are binding
   /// (this kind of obviates the Env, as itll be Var -> Var, but whatever.)
   BAddr(Var),
   /// The expression that created the continuation.
   KAddr(Expr),
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

   /// actually a join operation.
   pub fn insert(&self, a: Address, v: Val) -> Store {
      if let Address::BAddr(..) = a {
         Store {
            binds: self
               .binds
               .update(a.clone(), Val::from_old(self.binds.get(&a), v)),
            konts: self.konts.clone(),
         }
      } else {
         panic!("Not given a binding-addr with the value. {:?}", a);
      }
   }

   pub fn insertk(&self, a: Address, k: Kont) -> Store {
      if let Address::KAddr(..) = a {
         Store {
            binds: self.binds.clone(),
            konts: match self.konts.get(&a) {
               Some(old) => self.konts.update(a, old.clone().update(k)),
               None => self.konts.update(a, im::HashSet::unit(k)),
            },
         }
      } else {
         panic!("Not given a kont-addr with the kont. {:?}", k);
      }
   }

   pub fn get(&self, k: &Address) -> Val {
      match k {
         Address::BAddr(..) => self.binds.get(k).cloned().expect("No BAddr found."),
         Address::KAddr(..) => panic!("Should only be getting Bindings: {:?}", k),
      }
   }

   pub fn getk(&self, k: &Address) -> im::HashSet<Kont> {
      match k {
         Address::BAddr(..) => panic!("Should only be getting Konts: {:?}", k),
         Address::KAddr(..) => self.konts.get(k).cloned().expect("No KAddr found."),
      }
   }
}

impl Val {
   pub fn new(cv: ConcreteVal) -> Val {
      match cv {
         ConcreteVal::Closure(clo) => Val {
            closures: im::HashSet::unit(clo),
            vals: Err(false),
         },
         other => Val {
            closures: im::HashSet::new(),
            vals: Ok(other),
         },
      }
   }

   pub fn top() -> Val {
      Val {
         closures: im::HashSet::new(),
         vals: Err(true),
      }
   }

   fn from_old(old: Option<&Val>, new: Val) -> Val {
      match old {
         None => new,
         Some(old) => Val {
            closures: old.closures.clone().union(new.closures),
            vals: match (old.vals.clone(), new.vals) {
               (Err(false), Err(false)) => Err(false),
               (_, Err(true)) => Err(true),
               (Err(true), _) => Err(true),
               (Err(false), nf) => nf,
               (nf, Err(false)) => nf,
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

/// More like 'val may be a list'.
/// Will tell if a given value can ever be a proper-list, meaning null-terminated.
/// Some(true) -> Will always be a list
/// Some(false) -> Will never be a list
/// None -> Maybe!
pub fn val_maybe_list(val: &Val) -> Option<bool> {
   match val.vals {
      // maybe! Cant hurt to just run more branches!
      Err(true) => None,
      // never inhabited by a non-closure value, couldnt be a list.
      Err(false) => Some(false),
      Ok(ref v) => {
         if !matches!(v, ConcreteVal::Cons(_, _) | ConcreteVal::Null) {
            return Some(false); // the value inhabited wasnt a proper-list.
         }
         let mut cur = v;
         while let ConcreteVal::Cons(_, cdr) = cur {
            cur = match cdr.vals {
               // dont know rest of the list
               Err(true) => {
                  return None;
               }
               // ended by a only-closure, not a proper list.
               Err(false) => {
                  return Some(false);
               }
               Ok(ref ccdr) => ccdr,
            }
         }
         match cur {
            ConcreteVal::Null => Some(true),
            _ => Some(false),
         }
      }
   }
}

pub fn make_scm_list(vals: Vec<Val>) -> Val {
   let mut lst = Val::new(ConcreteVal::Null);
   for v in vals.into_iter().rev() {
      lst = Val::new(ConcreteVal::Cons(Box::new(v), Box::new(lst)));
   }
   lst
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
pub fn balloc(v: Var) -> Address {
   Address::BAddr(v)
}

pub fn kalloc(e: Expr) -> Address {
   Address::KAddr(e)
}

pub fn apply_state(val: Val, store: Store, kaddr: Address) -> State {
   State::Apply(ApplyState::new(val, store, kaddr))
}

pub fn eval_state(ctrl: Expr, env: Env, store: Store, kaddr: Address) -> State {
   State::Eval(EvalState::new(ctrl, env, store, kaddr))
}

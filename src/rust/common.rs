use std::fmt;

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum State {
   Eval(SExprState),
   Apply(ValState),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct SExprState {
   pub ctrl: SExpr,
   pub env: Env,
   pub kont_addr: Addr,
   pub time: Time,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct ValState {
   pub ctrl: Val,
   pub env: Env,
   pub kont_addr: Addr,
   pub time: Time,
}

#[derive(Hash, Clone, PartialEq, Eq)]
pub enum SExpr {
   List(Vec<SExpr>),
   Atom(String),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Env(pub im::HashMap<Var, Addr>);

/// Store isnt clonable, its global!
#[derive(Debug)]
pub struct Store(pub std::collections::HashMap<Addr, Val>);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum Val {
   Null, // mostly used as end-of-list sentinel value.
   Void, // returned by things like `(set! x e)`, (prim println), etc.
   Closure(Closure),
   Number(i64),
   Kont(Kont),
   Boolean(bool),
   Quote(SExpr),
   Cons(Box<Val>, Box<Val>),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Closure(pub CloType, pub SExpr, pub Env);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum CloType {
   MultiArg(Vec<Var>),
   VarArg(Var),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum Kont {
   Empty,
   If(SExpr, SExpr, Env, Addr),
   Let(Vec<Var>, Vec<Val>, Vec<SExpr>, SExpr, Env, Addr),
   Callcc(Env, Addr),
   Set(Var, Env, Addr),
   Prim(Prim, Vec<Val>, Vec<SExpr>, Env, Addr),
   ApplyPrim(Prim, Env, Addr),
   ApplyList(Option<Box<Val>>, SExpr, Env, Addr),
   App(Vec<Val>, Vec<SExpr>, Env, Addr),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Var(pub String);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Addr(pub u64);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Time(pub u64);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Prim(pub String);

pub trait Alloc {
   fn alloc(&self, offset: u64) -> Addr;
   fn tick(&self, amt: u64) -> Time;
}

impl SExprState {
   pub fn new(ctrl: SExpr, env: Env, kont_addr: Addr, time: Time) -> SExprState {
      SExprState {
         ctrl,
         env,
         kont_addr,
         time,
      }
   }
}

impl Alloc for SExprState {
   fn alloc(&self, offset: u64) -> Addr {
      let SExprState { time: Time(t), .. } = self;
      Addr(*t + offset)
   }

   /// Need to give an amount cause multiple allocations
   /// can happen in a single frame (e.g. function application)
   fn tick(&self, amt: u64) -> Time {
      let SExprState { time: Time(t), .. } = self;
      Time(t + amt)
   }
}

impl ValState {
   pub fn new(ctrl: Val, env: Env, kont_addr: Addr, time: Time) -> ValState {
      ValState {
         ctrl,
         env,
         kont_addr,
         time,
      }
   }
}

impl Alloc for ValState {
   fn alloc(&self, offset: u64) -> Addr {
      let ValState { time: Time(t), .. } = self;
      Addr(*t + offset)
   }

   /// Need to give an amount cause multiple allocations
   /// can happen in a single frame (e.g. function application)
   fn tick(&self, amt: u64) -> Time {
      let ValState { time: Time(t), .. } = self;
      Time(t + amt)
   }
}

impl Alloc for State {
   fn alloc(&self, offset: u64) -> Addr {
      match self {
         State::Eval(s) => s.alloc(offset),
         State::Apply(v) => v.alloc(offset),
      }
   }

   fn tick(&self, amt: u64) -> Time {
      match self {
         State::Eval(s) => s.tick(amt),
         State::Apply(v) => v.tick(amt),
      }
   }
}

impl Env {
   pub fn insert(&self, k: Var, v: Addr) -> Env {
      let mut newenv = self.0.clone();
      newenv.insert(k, v);
      Env(newenv)
   }

   pub fn get(&self, var: Var) -> Option<Addr> {
      self.0.get(&var).cloned()
   }
}

impl Store {
   pub fn add_to_store<A: Alloc>(&mut self, v: Val, st: &A) -> Addr {
      self.add_to_store_offset(v, st, 0)
   }

   pub fn add_to_store_offset<A: Alloc>(&mut self, v: Val, st: &A, offset: u64) -> Addr {
      let addr = st.alloc(offset);
      self.0.insert(addr.clone(), v);
      addr
   }

   pub fn get(&self, addr: Addr) -> Option<Val> {
      self.0.get(&addr).cloned()
   }

   pub fn set(&mut self, addr: Addr, val: Val) -> Option<Val> {
      self.0.insert(addr, val)
   }
}

impl fmt::Debug for SExpr {
   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      match self {
         SExpr::List(ref list) => {
            write!(f, "(")?;
            for (i, e) in list.iter().enumerate() {
               write!(f, "{:?}", e)?;
               if i + 1 != list.len() {
                  write!(f, " ")?;
               }
            }
            write!(f, ")")
         }
         SExpr::Atom(ref atom) => write!(f, "{}", atom),
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

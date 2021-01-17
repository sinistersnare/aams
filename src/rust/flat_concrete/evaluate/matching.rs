use crate::flat_concrete::common::{LambdaArgType, Var};
use crate::Expr;

/// Expression Matching Code, to see if an Expr
/// matches some syntax.

/// (quote e)
pub fn matches_quote_expr(list: &[Expr]) -> Option<Expr> {
   if list.len() == 2 && list[0] == Expr::Atom("quote".to_string()) {
      Some(list[1].clone())
   } else {
      None
   }
}

/// (apply e e)
pub fn matches_apply_expr(list: &[Expr]) -> Option<(Expr, Expr)> {
   if list.len() == 3 && list[0] == Expr::Atom("apply".to_string()) {
      Some((list[1].clone(), list[2].clone()))
   } else {
      None
   }
}

/// (lambda (x ...) e)
/// (lambda x e)
pub fn matches_lambda_expr(list: &[Expr]) -> Option<(LambdaArgType, Expr)> {
   if list.len() == 3
      && (list[0] == Expr::Atom("lambda".to_string()) || list[0] == Expr::Atom("λ".to_string()))
   {
      match list[1] {
         Expr::List(ref args) => {
            let mut argvec = Vec::with_capacity(args.len());
            for arg_sexpr in args {
               match arg_sexpr {
                  Expr::List(_) => {
                     panic!("Unexpected list in argument position");
                  }
                  Expr::Atom(ref arg) => {
                     argvec.push(Var(arg.clone()));
                  }
               };
            }
            Some((LambdaArgType::FixedArg(argvec), list[2].clone()))
         }
         Expr::Atom(ref var) => Some((LambdaArgType::VarArg(Var(var.clone())), list[2].clone())),
      }
   } else {
      None
   }
}

/// (if e e e)
pub fn matches_if_expr(list: &[Expr]) -> Option<(Expr, Expr, Expr)> {
   if list.len() == 4 && list[0] == Expr::Atom("if".to_string()) {
      Some((list[1].clone(), list[2].clone(), list[3].clone()))
   } else {
      None
   }
}

/// (let ([x e] ...) e)
pub fn matches_let_expr(list: &[Expr]) -> Option<(Vec<Var>, Vec<Expr>, Expr)> {
   if list.len() == 3 && list[0] == Expr::Atom("let".to_string()) {
      match list[1] {
         Expr::List(ref outer) => {
            let mut vars = Vec::with_capacity(outer.len());
            let mut exprs = Vec::with_capacity(outer.len());
            for binding in outer {
               match binding {
                  Expr::List(ref entry) => {
                     if entry.len() != 2 {
                        panic!("Let entry must only have 2 elements.");
                     }
                     match entry[0] {
                        Expr::List(_) => {
                           panic!("Binding name must be an atom.");
                        }
                        Expr::Atom(ref v) => {
                           vars.push(Var(v.clone()));
                           exprs.push(entry[1].clone());
                        }
                     }
                  }
                  Expr::Atom(_) => {
                     panic!("Bindings are len-2 lists, not atoms.");
                  }
               }
            }
            Some((vars, exprs, list[2].clone()))
         }
         Expr::Atom(_) => {
            panic!("Let takes a binding list, not a single arg");
         }
      }
   } else {
      None
   }
}

/// (call/cc e)
pub fn matches_callcc_expr(list: &[Expr]) -> Option<Expr> {
   if list.len() == 2 && list[0] == Expr::Atom("call/cc".to_string()) {
      Some(list[1].clone())
   } else {
      None
   }
}

/// (set! x e)
pub fn matches_setbang_expr(list: &[Expr]) -> Option<(Var, Expr)> {
   if list.len() == 3 && list[0] == Expr::Atom("set!".to_string()) {
      match list[1] {
         Expr::Atom(ref x) => Some((Var(x.clone()), list[2].clone())),
         Expr::List(_) => {
            panic!("set! takes a var then an expression");
         }
      }
   } else {
      None
   }
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

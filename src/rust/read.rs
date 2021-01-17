//! A Parser of Scheme types.
//! `Expr` is the AST type here that will be executed.

use std::fmt;

use combine::error::ParseError;
use combine::parser::char::{char, space};
use combine::stream::Stream;
use combine::{
   between, choice, many1, parser, satisfy, sep_by, skip_many, skip_many1, token, Parser,
};

#[derive(Hash, Clone, PartialEq, Eq)]
pub enum Expr {
   List(Vec<Expr>),
   Atom(String),
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

fn expr_<Input>() -> impl Parser<Input, Output = Expr>
where
   Input: Stream<Token = char>,
   Input::Error: ParseError<Input::Token, Input::Range, Input::Position>,
{
   let atom_char = || {
      satisfy(|ch: char| {
         matches!(ch,
      '0'..='9' | '<'..='Z' | 'a'..='z'
      | '~' | '!' | '$' | '%' | '^' | '&'
      | '*' | '_' | '+' | ':' | '/' | '-' | 'λ' | '#')
      })
   };

   let whitespace = || {
      let comment = (token(';'), skip_many(satisfy(|c| c != '\n'))).map(|_| ());
      // Wrap the `spaces().or(comment)` in  `skip_many` so
      // that it skips alternating whitespace and comments
      skip_many(skip_many1(space()).or(comment))
   };

   // TODO better parsing of atom,
   // some characters only allowed at start like '#'s
   // so have something like optional(char('#')).then(atom_body())
   // but that doesnt work cause fuck if i know.
   let atom_body = || many1(atom_char());
   let atom = atom_body();

   let lex_char = |c| char(c).skip(whitespace());

   let space_separated_exprs = || sep_by(expr(), whitespace());
   let list = between(lex_char('('), lex_char(')'), space_separated_exprs());
   let sqlist = between(lex_char('['), lex_char(']'), space_separated_exprs());
   choice((
      atom.map(Expr::Atom),
      list.map(Expr::List),
      sqlist.map(Expr::List),
   ))
   .skip(whitespace())
}

parser! {
   fn expr[Input]()(Input) -> Expr
   where [Input: Stream<Token = char>]
   {
      expr_()
   }
}

pub fn parse_expr(input: &str) -> Result<(Expr, &str), combine::error::StringStreamError> {
   expr().parse(input)
}

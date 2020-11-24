//! A Parser of Scheme types.
//! `SExpr` is the AST type here that will be executed.

use combine::error::ParseError;
use combine::parser::char::{char, space};
use combine::stream::Stream;
use combine::{
   between, choice, many1, parser, satisfy, sep_by, skip_many, skip_many1, token, Parser,
};

use crate::common::SExpr;

fn expr_<Input>() -> impl Parser<Input, Output = SExpr>
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
      atom.map(SExpr::Atom),
      list.map(SExpr::List),
      sqlist.map(SExpr::List),
   ))
   .skip(whitespace())
}

parser! {
   fn expr[Input]()(Input) -> SExpr
   where [Input: Stream<Token = char>]
   {
      expr_()
   }
}

pub fn parse_expr(input: &str) -> Result<(SExpr, &str), combine::error::StringStreamError> {
   expr().parse(input)
}

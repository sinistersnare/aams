//! A shitty scheme interpreter that I made without
//! looking at too much inspiration
//! JK I ENDED UP USING https://github.com/rui314/minilisp/blob/master/minilisp.c
//! FOR A LOT OF INSPIRATION!!!! TY MINILISP!
//!
//! I made this to study different continuation implementations.
#[macro_use]
extern crate lazy_static;
extern crate combine;
extern crate im;

use std::env;
use std::fs;

mod common;
mod eval;
mod prims;
mod read;

use crate::common::State;
use crate::eval::evaluate;
use crate::read::parse_expr;

fn main() {
   if let Some(filename) = env::args().nth(1) {
      exec_string(&fs::read_to_string(filename).expect("Could not read file"))
   } else {
      start_repl();
   };
}

fn start_repl() {
   use std::io::{stdin, stdout, Write};
   let mut input = String::new();

   loop {
      print!("> ");
      stdout().flush().expect("Flushed... poorly?");
      stdin()
         .read_line(&mut input)
         .expect("Did not enter a full string.");
      exec_string(&input);
      input.clear();
   }
}

fn exec_string(program: &str) {
   let parsed = parse_expr(program.trim());
   match parsed {
      Ok((sexpr, _)) => {
         let (states, _store) = evaluate(sexpr);
         let fin_state = states.last().unwrap();
         match fin_state {
            State::Eval(e) => panic!("Howd we end with eval? {:?}", e),
            State::Apply(v) => println!("{:?}", v.ctrl),
         }
      }
      Err(e) => println!("Error Parsing: {:?}", e),
   };
}

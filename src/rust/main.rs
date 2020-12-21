//!
//! A Scheme interpreter based on the formalization found in this repo.
//!

#[macro_use]
extern crate lazy_static;
extern crate combine;
extern crate im;

use std::env;
use std::fs;

mod common;
mod evaluate;
mod prims;
mod read;

use crate::common::State;
use crate::evaluate::evaluate;
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
         let states = evaluate(sexpr);
         let fin_state = states.last().unwrap();
         match fin_state {
            State::Eval(e) => panic!("Howd we end with eval? {:?}", e),
            State::Apply(v) => println!("{:?}", v.val),
         }
      }
      Err(e) => println!("Error Parsing: {:?}", e),
   };
}

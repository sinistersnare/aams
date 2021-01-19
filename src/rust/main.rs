//!
//! A Scheme interpreter based on the formalization found in this repo.
//!

#[macro_use]
extern crate lazy_static;
extern crate combine;
extern crate im;

use std::env;
use std::fs;

// To use a different machine
// change the name of the machine module, and the module in the evaluate use.
// not my best solution but it works well enough!

pub mod matching;
pub mod common;
mod flat_abstract;
mod read;

use crate::read::parse_expr;
use flat_abstract::evaluate;

fn main() {
   if let Some(filename) = env::args().nth(1) {
      exec_str(&fs::read_to_string(filename).expect("Could not read file"))
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
      exec_str(&input);
      input.clear();
   }
}

fn exec_str(program: &str) {
   let parsed = parse_expr(program.trim());
   match parsed {
      Ok((sexpr, _)) => {
         let states = evaluate(sexpr);
         println!("All states: {:#?}", states);
      }
      Err(e) => println!("Error Parsing: {:?}", e),
   };
}

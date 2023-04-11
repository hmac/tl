use std::io::stdin;
use std::io::read_to_string;

mod ast;
mod parser;

fn main() {
    let input = read_to_string(stdin()).unwrap();
    let mut parser = parser::Parser::new(input);
    match parser.parse() {
        Ok(ast) => {
            dbg!(ast);
        },
        Err(error) => {
            println!("Error:");
            parser::print_error(&parser.into_input(), error);
        }
    }
}

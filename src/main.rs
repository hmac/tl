use std::io::stdin;
use std::io::read_to_string;

use tl::{ast, parser, typechecker};

fn main() {
    let input = read_to_string(stdin()).unwrap();
    let mut parser = parser::Parser::new(input);
    match parser.parse() {
        Ok(ast) => {
            let mut typechecker = typechecker::Typechecker::new();

            for decl in &ast {
                match decl {
                    ast::Decl::Type { name, constructors, loc } => {
                        typechecker.register_type(&name, &constructors, *loc).unwrap();
                    }
                    ast::Decl::Func { name, r#type, loc, .. } => {
                        typechecker.register_func(&name, &r#type, *loc).unwrap();
                    }
                }
            }

            typechecker.check_all_types().unwrap();

            for decl in ast {
                match decl {
                    ast::Decl::Func {  r#type, body, .. } => {
                        if let Err(error) = typechecker.check_func(&body, &r#type) {
                            println!("Error:\n");
                            ast::print_error(&parser.into_input(), error);
                            return;
                        }
                    }
                    _ => {}
                }
            }

            println!("Typecheck successful.");
        },
        Err(error) => {
            println!("Error:\n");
            ast::print_error(&parser.into_input(), error);
        }
    }
}

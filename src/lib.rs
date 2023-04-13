pub mod ast;
pub mod parser;
pub mod typechecker;
pub mod interpreter;
mod local_variables;

use std::io::Write;

pub fn run<W:Write>(input: String, output: &mut W) -> std::io::Result<()> {
    let mut parser = parser::Parser::new(input);
    match parser.parse() {
        Ok(ast) => {
            let mut typechecker = typechecker::Typechecker::new();

            for decl in &ast {
                match decl {
                    ast::Decl::Type {
                        name,
                        constructors,
                        loc,
                    } => {
                        if let Err(error) = typechecker.register_type(&name, &constructors, *loc) {
                            writeln!(output, "Error:\n")?;
                            ast::print_error(output, &parser.into_input(), error);
                            return Ok(());
                        }
                    }
                    ast::Decl::Func {
                        name, r#type, loc, ..
                    } => {
                        typechecker.register_func(&name, &r#type, *loc).unwrap();
                    }
                }
            }

            typechecker.check_all_types().unwrap();

            for decl in &ast {
                match decl {
                    ast::Decl::Func { r#type, body, .. } => {
                        if let Err(error) = typechecker.check_func(&body, &r#type) {
                            writeln!(output, "Error:\n")?;
                            ast::print_error(output, &parser.into_input(), error);
                            return Ok(());
                        }
                    }
                    _ => {}
                }
            }

            let mut interpreter = interpreter::Interpreter::new();

            for decl in &ast {
                match decl {
                    ast::Decl::Func { name, body, .. } => {
                        interpreter.register_func(name, &body);
                    }
                    _ => {}
                }
            }

            for decl in &ast {
                match decl {
                    ast::Decl::Func { name, body, .. } if name == "main" => {
                        let locals = local_variables::LocalVariables::new();
                        match interpreter.eval(&locals, &body) {
                            Err(error) => {
                                writeln!(output, "Error: {:?}\n", error)?;
                            }
                            Ok(result) => {
                                writeln!(output, "{}", result)?;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        Err(error) => {
            writeln!(output, "Error:\n")?;
            ast::print_error(output, &parser.into_input(), error);
        }
    }
    Ok(())
}

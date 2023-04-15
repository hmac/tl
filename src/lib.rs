pub mod ast;
pub mod parser;
pub mod typechecker;
pub mod interpreter;
mod local_variables;

use std::io::Write;
use std::io;
use std::path::{Path, PathBuf};

use ast::Decl;
use interpreter::Interpreter;

#[derive(Debug)]
pub enum Error {
    Parse,
    Type,
    Eval,
    IO(io::Error)
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::IO(error)
    }
}

pub struct Runner<'a> {
    path: PathBuf,
    source: String,
    ast: Vec<Decl>,
    interpreter: Interpreter,
    output: Box<dyn Write + 'a>
}

impl<'a> Runner<'a> {
    pub fn from_path<W: Write + 'a>(path: &Path, output: W) -> Result<Self, Error> {
        let source = std::fs::read_to_string(path)?;

        Self::new(path, source, output)
    }

    pub fn new<W: Write + 'a>(path: &Path, source: String, mut output: W) -> Result<Self, Error> {

        let mut parser = parser::Parser::new(source.clone());
        match parser.parse() {
            Ok(ast) => {
                let mut typechecker = typechecker::Typechecker::new();

                for decl in &ast {
                    match decl {
                        Decl::Type {
                            name,
                            constructors,
                            loc,
                        } => {
                            if let Err(error) = typechecker.register_type(&name, &constructors, *loc) {
                                writeln!(output, "Error:\n")?;
                                ast::print_error(&mut output, &source, error);
                                return Err(Error::Type);
                            }
                        }
                        Decl::Func {
                            name, r#type, loc, ..
                        } => {
                            typechecker.register_func(&name, &r#type, *loc).unwrap();
                        }
                    }
                }

                typechecker.check_all_types().unwrap();

                for decl in &ast {
                    match decl {
                        Decl::Func { r#type, body, .. } => {
                            if let Err(error) = typechecker.check_func(&body, &r#type) {
                                writeln!(output, "Error:\n")?;
                                ast::print_error(&mut output, &parser.into_input(), error);
                                return Err(Error::Type);
                            }
                        }
                        _ => {}
                    }
                }

                let mut interpreter = interpreter::Interpreter::new();

                for decl in &ast {
                    match decl {
                        Decl::Func { name, body, .. } => {
                            interpreter.register_func(name, &body);
                        }
                        _ => {}
                    }
                }

                Ok(Self {
                    path: path.to_owned(),
                    source,
                    ast,
                    interpreter,
                    output: Box::new(output)
                })

            }
            Err(error) => {
                writeln!(output, "Error:\n")?;
                ast::print_error(&mut output, &parser.into_input(), error);
                return Err(Error::Parse);
            }
        }

    }

    pub fn run(&mut self, func_name: &str) -> Result<interpreter::Value, Error> {
        let func = &self.ast.iter().find_map(|decl| {
            match decl {
                Decl::Func { name, body, .. } if name == func_name => Some(body),
                _ => None
            }
        });
        match func {
            Some(func_body) => {
                match self.interpreter.eval(&local_variables::LocalVariables::new(), func_body) {
                    Ok(value) => Ok(value),
                    Err(error) => {
                        writeln!(&mut self.output, "Error:\n")?;
                        writeln!(&mut self.output, "{:?}", error)?;
                        Err(Error::Eval)
                    }
                }
            }
            None => {
                let error = interpreter::Error::UndefinedVariable(func_name.to_string());
                writeln!(&mut self.output, "Error:\n")?;
                writeln!(&mut self.output, "{:?}", error)?;
                Err(Error::Eval)
            }
        }
    }
}

// pub fn run<W:Write>(input: String, output: &mut W) -> std::io::Result<()> {
//     let mut parser = parser::Parser::new(input);
//     match parser.parse() {
//         Ok(ast) => {
//             let mut typechecker = typechecker::Typechecker::new();

//             for decl in &ast {
//                 match decl {
//                     Decl::Type {
//                         name,
//                         constructors,
//                         loc,
//                     } => {
//                         if let Err(error) = typechecker.register_type(&name, &constructors, *loc) {
//                             writeln!(output, "Error:\n")?;
//                             ast::print_error(output, &parser.into_input(), error);
//                             return Ok(());
//                         }
//                     }
//                     Decl::Func {
//                         name, r#type, loc, ..
//                     } => {
//                         typechecker.register_func(&name, &r#type, *loc).unwrap();
//                     }
//                 }
//             }

//             typechecker.check_all_types().unwrap();

//             for decl in &ast {
//                 match decl {
//                     Decl::Func { r#type, body, .. } => {
//                         if let Err(error) = typechecker.check_func(&body, &r#type) {
//                             writeln!(output, "Error:\n")?;
//                             ast::print_error(output, &parser.into_input(), error);
//                             return Ok(());
//                         }
//                     }
//                     _ => {}
//                 }
//             }

//             let mut interpreter = interpreter::Interpreter::new();

//             for decl in &ast {
//                 match decl {
//                     Decl::Func { name, body, .. } => {
//                         interpreter.register_func(name, &body);
//                     }
//                     _ => {}
//                 }
//             }

//             for decl in &ast {
//                 match decl {
//                     Decl::Func { name, body, .. } if name == "main" => {
//                         let locals = local_variables::LocalVariables::new();
//                         match interpreter.eval(&locals, &body) {
//                             Err(error) => {
//                                 writeln!(output, "Error: {:?}\n", error)?;
//                             }
//                             Ok(result) => {
//                                 writeln!(output, "{}", result)?;
//                             }
//                         }
//                     }
//                     _ => {}
//                 }
//             }
//         }
//         Err(error) => {
//             writeln!(output, "Error:\n")?;
//             ast::print_error(output, &parser.into_input(), error);
//         }
//     }
//     Ok(())
// }

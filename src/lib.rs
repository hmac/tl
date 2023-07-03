pub mod ast;
mod compiler;
pub mod interpreter;
mod local_variables;
pub mod parser;
mod stack;
pub mod typechecker;
mod vm;

use std::io;
use std::io::Write;
use std::path::{Path, PathBuf};

use ast::Decl;
use interpreter::Interpreter;
use tracing::{debug, warn};

#[derive(Debug)]
pub enum Error {
    Parse,
    Type,
    Eval,
    IO(io::Error),
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
    vm: vm::Vm,
    output: Box<dyn Write + 'a>,
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
                            params,
                            constructors,
                            loc,
                        } => {
                            if let Err(error) =
                                typechecker.register_type(&name, &params, &constructors, *loc)
                            {
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
                        Decl::Test { .. } => {}
                    }
                }

                if let Err(error) = typechecker.check_all_types() {
                    writeln!(output, "Error:\n")?;
                    ast::print_error(&mut output, &parser.into_input(), error);
                    return Err(Error::Type);
                }

                for decl in &ast {
                    match decl {
                        Decl::Func { r#type, body, .. } => {
                            if let Err(error) = typechecker.check_func(&body, &r#type) {
                                writeln!(output, "Error:\n")?;
                                ast::print_error(&mut output, &parser.into_input(), error);
                                return Err(Error::Type);
                            }
                        }
                        Decl::Test { name, body, .. } => {
                            if let Err(error) =
                                typechecker.check_func(&body, &ast::SourceType::Bool((0, 0)))
                            {
                                writeln!(output, "Error in test {name}:\n")?;
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

                let mut compiler = compiler::Compiler::new();

                for decl in &ast {
                    match decl {
                        Decl::Func { name, body, .. } => {
                            compiler.compile_func(name, &body).unwrap();
                        }
                        Decl::Test { name, body, .. } => {
                            // Test names may overlap with function names, so do some hacky
                            // namespacing.
                            // TODO: proper namespacing for tests
                            compiler
                                .compile_func(&format!("test_{name}"), &body)
                                .unwrap();
                        }
                        _ => {}
                    }
                }

                let vm = vm::Vm::from_compiler(compiler);

                Ok(Self {
                    path: path.to_owned(),
                    source,
                    ast,
                    interpreter,
                    vm,
                    output: Box::new(output),
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
        let func = &self.ast.iter().find_map(|decl| match decl {
            Decl::Func { name, body, .. } if name == func_name => Some(body),
            _ => None,
        });

        let (iloc, _) = self.vm.functions.get(func_name).unwrap();
        dbg!(&self.vm.prog);
        self.vm.run(*iloc).unwrap();

        match func {
            Some(func_body) => {
                match self
                    .interpreter
                    .eval(&local_variables::LocalVariables::new(), func_body)
                {
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

    pub fn run_tests(&mut self) -> Result<usize, Error> {
        let mut failures = 0;

        for decl in &self.ast {
            match decl {
                Decl::Test { name, .. } => {
                    debug!("running test {name}");
                    let test_name = format!("test_{name}");
                    let (block_id, _args) = self.vm.functions.get(&test_name).unwrap();
                    match self.vm.run(*block_id) {
                        Ok(result) => match result {
                            vm::Value::Int(_) => todo!(),
                            vm::Value::Bool(true) => {
                                writeln!(&mut self.output, "{name}: PASS\n")?;
                            }
                            vm::Value::Bool(false) => {
                                writeln!(&mut self.output, "{name}: FAIL\n")?;
                                failures += 1;
                            }
                            _ => {
                                panic!("Unexpected result from test {name}: {result}");
                            }
                        },
                        Err(error) => {
                            panic!("Error running test {name}: {error:?}");
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(failures)
    }
}

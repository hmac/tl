pub mod ast;
mod compiler;
mod local_variables;
pub mod parser;
mod stack;
pub mod typechecker;
mod vm;

use std::collections::HashMap;
use std::io;
use std::io::Write;
use std::path::{Path, PathBuf};

use ast::{Decl, GlobalName, HasLoc, Loc};
use tracing::debug;
use typechecker::Typechecker;

#[derive(Debug)]
pub enum Error {
    Parse,
    Type,
    Eval,
    IO(io::Error),
    ImportCycle(PathBuf),
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::IO(error)
    }
}

struct ImportPathDoesNotExist {
    loc: Loc,
}

impl HasLoc for ImportPathDoesNotExist {
    fn loc(&self) -> ast::Loc {
        self.loc
    }
}

impl std::fmt::Display for ImportPathDoesNotExist {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "no file matches this import path")
    }
}

pub struct Runner<'a> {
    // Maps file paths to their parsed contents
    files: HashMap<PathBuf, Vec<Decl>>,
    // The path of the main file
    path: PathBuf,
    output: Box<dyn Write + 'a>,
    typechecker: Typechecker,
}

impl<'a> Runner<'a> {
    pub fn from_path<W: Write + 'a>(path: &Path, output: W) -> Result<Self, Error> {
        let source = std::fs::read_to_string(path)?;

        Self::new(path, source, output)
    }

    pub fn new<W: Write + 'a>(path: &Path, source: String, output: W) -> Result<Self, Error> {
        let mut this = Self {
            files: HashMap::new(),
            path: path.to_path_buf(),
            output: Box::new(output),
            typechecker: Typechecker::new(),
        };
        this.load_file_source(path, source)?;
        Ok(this)
    }

    fn load_file(&mut self, path: &Path) -> Result<(), Error> {
        self.load_file_source(path, std::fs::read_to_string(path)?)
    }

    fn load_file_source(&mut self, path: &Path, source: String) -> Result<(), Error> {
        let path = path.canonicalize()?;

        let mut parser = parser::Parser::new(source.clone());
        match parser.parse() {
            Ok(ast) => {
                // Process all imports first
                let mut imports = HashMap::new();
                for decl in &ast {
                    match decl {
                        Decl::Import {
                            name,
                            path: import_path,
                            path_loc,
                            ..
                        } => {
                            let abs_path = match path.parent() {
                                None => import_path.into(),
                                Some(dir) => match dir.join(&import_path).canonicalize() {
                                    Ok(p) => Ok(p),
                                    Err(e) => {
                                        writeln!(self.output, "Error:\n")?;
                                        let error = ImportPathDoesNotExist { loc: *path_loc };
                                        ast::print_error(&mut self.output, &source, error);
                                        Err(e)
                                    }
                                }?,
                            };
                            self.load_file(&abs_path)?;
                            imports.insert(name.to_string(), abs_path);
                        }
                        _ => {}
                    }
                }
                self.typechecker.imports.insert(&path, imports);

                // TODO: figure out if/how we compile all decls in all imports

                // Register types with the typechecker
                for decl in &ast {
                    match decl {
                        Decl::Type {
                            name,
                            params,
                            constructors,
                            loc,
                        } => {
                            if let Err(error) = self.typechecker.register_type(
                                &path,
                                &name,
                                &params,
                                &constructors,
                                *loc,
                            ) {
                                writeln!(self.output, "Error:\n")?;
                                ast::print_error(&mut self.output, &source, error);
                                return Err(Error::Type);
                            }
                        }
                        _ => {}
                    }
                }
                // Register function signatures with the typechecker
                for decl in &ast {
                    match decl {
                        Decl::Func {
                            name, r#type, loc, ..
                        } => {
                            if let Err(error) =
                                self.typechecker.register_func(&path, &name, &r#type, *loc)
                            {
                                writeln!(self.output, "Error:\n")?;
                                ast::print_error(
                                    &mut self.output,
                                    &source,
                                    error.with_path(Some(&path)),
                                );
                                return Err(Error::Type);
                            }
                        }
                        _ => {}
                    }
                }

                if let Err(error) = self.typechecker.check_all_types() {
                    writeln!(self.output, "Error:\n")?;
                    ast::print_error(&mut self.output, &parser.into_input(), error);
                    return Err(Error::Type);
                }

                // Check function and test bodies against their type
                for decl in &ast {
                    match decl {
                        Decl::Func { r#type, body, .. } => {
                            if let Err(error) = self.typechecker.check_func(&path, &body, &r#type) {
                                writeln!(self.output, "Error:\n")?;
                                ast::print_error(
                                    &mut self.output,
                                    &parser.into_input(),
                                    error.with_path(Some(&path)),
                                );
                                return Err(Error::Type);
                            }
                        }
                        Decl::Test { name, body, .. } => {
                            if let Err(error) = self.typechecker.check_func(
                                &path,
                                &body,
                                &ast::SourceType::Bool((0, 0)),
                            ) {
                                writeln!(self.output, "Error in test {name}:\n")?;
                                ast::print_error(&mut self.output, &parser.into_input(), error);
                                return Err(Error::Type);
                            }
                        }
                        _ => {}
                    }
                }

                self.files.insert(path.into(), ast);

                // We compile the root file after loading and typechecking all imports is done.

                Ok(())
            }
            Err(error) => {
                writeln!(self.output, "Error:\n")?;
                ast::print_error(&mut self.output, &parser.into_input(), error);
                Err(Error::Parse)
            }
        }
    }

    fn compile(&self) -> Result<compiler::Compiler, Error> {
        let mut compiler = compiler::Compiler::new(self.typechecker.imports.clone());

        // It doesn't matter what order we compile the functions in
        for (path, ast) in self.files.iter() {
            for decl in ast {
                match decl {
                    Decl::Func { name, body, .. } => {
                        compiler.compile_func(path, &name, &body).unwrap();
                    }
                    Decl::Test { name, body, .. } => {
                        // Test names may overlap with function names, so do some hacky
                        // namespacing.
                        // TODO: proper namespacing for tests
                        compiler
                            .compile_func(path, &format!("test_{name}"), &body)
                            .unwrap();
                    }
                    _ => {}
                }
            }
        }

        Ok(compiler)
    }

    pub fn run(&mut self, func_name: &str) -> Result<vm::Value, Error> {
        let compiler = self.compile()?;
        let vm = vm::Vm::from_compiler(compiler);

        let func_name =
            GlobalName::named(&self.path.canonicalize().unwrap(), func_name).to_string();
        match vm.functions.get(&func_name) {
            Some((func_instr_loc, _)) => match vm.run(*func_instr_loc) {
                Ok(value) => Ok(value),
                Err(error) => {
                    writeln!(&mut self.output, "Error:\n")?;
                    writeln!(&mut self.output, "{:?}", error)?;
                    Err(Error::Eval)
                }
            },
            None => {
                let error = vm::Error::UndefinedVariable(func_name.to_string());
                writeln!(&mut self.output, "Error:\n")?;
                writeln!(&mut self.output, "{:?}", error)?;
                Err(Error::Eval)
            }
        }
    }

    pub fn run_tests(&mut self) -> Result<usize, Error> {
        let compiler = self.compile()?;
        let vm = vm::Vm::from_compiler(compiler);

        let mut failures = 0;

        let path = self.path.canonicalize().unwrap();
        for decl in self.files.get(&path).unwrap() {
            match decl {
                Decl::Test { name, .. } => {
                    debug!("running test {name}");
                    let test_name = GlobalName::named(&path, &format!("test_{name}")).to_string();
                    let (block_id, _args) = vm.functions.get(&test_name).unwrap();
                    match vm.run(*block_id) {
                        Ok(result) => match result {
                            vm::Value::Int(_) => todo!(),
                            vm::Value::Bool(true) => {
                                writeln!(&mut self.output, "PASS: {name}")?;
                            }
                            vm::Value::Bool(false) => {
                                writeln!(&mut self.output, "FAIL: {name}")?;
                                failures += 1;
                            }
                            // TODO: remove by adding bools to the AST
                            vm::Value::Constructor { name, args } if name == "True" => {
                                assert!(args.is_empty());
                                writeln!(&mut self.output, "PASS: {name}")?;
                            }
                            vm::Value::Constructor { name, args } if name == "False" => {
                                assert!(args.is_empty());
                                writeln!(&mut self.output, "FAIL: {name}")?;
                                failures += 1;
                            }
                            _ => {
                                panic!("Unexpected result from test {name}: {result:?}");
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

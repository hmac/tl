use std::collections::{HashMap, HashSet, VecDeque};

use crate::ast::*;
use crate::local_variables::LocalVariables;

const TYPE_INT: Type = Type::Int;

#[derive(Debug)]
pub enum Error {
    TypeAlreadyDefined(Loc, String),
    UnknownType(Loc, String),
    UnknownVariable(Loc, String),
    UnknownConstructor(Loc, String),
    EmptyMatch(Loc),
    ExpectedType {
        loc: Loc,
        expected: Type,
        actual: Type,
    },
    MatchBranchArgNumberMismatch {
        loc: Loc,
        number_of_args_in_branch: usize,
        number_of_args_in_constructor_type: usize,
    },
    CannotInferTypeOfFunctions(Loc),
    ExpectedFunctionType {
        loc: Loc,
        actual_type: Type,
    },
    DuplicateConstructor { existing: (Loc, Type), duplicate: TypeConstructor },
    CannotApplyNonFunction { loc: Loc, actual_type: Type },
    TooManyArgumentsInApplication { loc: Loc, max_number_of_arguments: usize, actual_number_of_arguments: usize },
}

impl HasLoc for Error {
    fn loc(&self) -> Loc {
        match self {
            Error::TypeAlreadyDefined(loc, _) => *loc,
            Error::UnknownType(loc, _) => *loc,
            Error::UnknownVariable(loc, _) => *loc,
            Error::UnknownConstructor(loc, _) => *loc,
            Error::EmptyMatch(loc) => *loc,
            Error::ExpectedType { loc, .. } => *loc,
            Error::MatchBranchArgNumberMismatch { loc, .. } => *loc,
            Error::CannotInferTypeOfFunctions(loc) => *loc,
            Error::ExpectedFunctionType { loc, .. } => *loc,
            Error::DuplicateConstructor { duplicate, .. } => duplicate.loc,
            Error::CannotApplyNonFunction { loc, .. } => *loc,
            Error::TooManyArgumentsInApplication { loc, .. } => *loc,
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Error::TypeAlreadyDefined(_, ty) => {
                write!(f, "the type '{ty}' has already been defined elsewhere")
            }
            Error::UnknownType(_, ty) => {
                write!(f, "unknown type '{ty}'")
            }
            Error::UnknownVariable(_, v) => {
                write!(f, "unknown variable '{v}'")
            }
            Error::UnknownConstructor(_, c) => {
                write!(f, "unknown constructor '{c}'")
            }
            Error::EmptyMatch(_) => {
                write!(f, "match expressions cannot be empty")
            }
            Error::ExpectedType {
                expected, actual, ..
            } => {
                write!(f, "expected this to have the type {expected}, but it actually has the type {actual}")
            }
            Error::MatchBranchArgNumberMismatch {
                number_of_args_in_branch,
                number_of_args_in_constructor_type,
                ..
            } => {
                write!(
                    f,
                    "the number of arguments in this match branch ({}) doesn't match the number of arguments in the constructor's type ({})",
                    number_of_args_in_branch,
                    number_of_args_in_constructor_type
                    )
            }
            Error::CannotInferTypeOfFunctions(_) => {
                write!(f, "this function needs a type annotation")
            }
            Error::ExpectedFunctionType { actual_type, .. } => {
                write!(
                    f,
                    "expected to have a function type, but its actual type is {actual_type}"
                )
            }
            Error::DuplicateConstructor { .. } => {
                write!(
                    f,
                    "this constructor conflicts with an existing constructor of the same name - constructor names must be globally unique",
                )
            }
            Error::CannotApplyNonFunction { actual_type, .. } => {
                write!(
                    f,
                    "this expression cannot be applied as a function, because it has type {actual_type}",
                )
            }
            Error::TooManyArgumentsInApplication { max_number_of_arguments, actual_number_of_arguments, .. } => {
                write!(
                    f,
                    "this function takes {max_number_of_arguments} {}, but is given {actual_number_of_arguments}",
                    if *max_number_of_arguments > 1 { "arguments" } else { "argument" }
                )
            }
        }
    }
}

pub struct Typechecker {
    constructors: HashMap<String, (Loc, Type)>,
    types: HashSet<String>,
    functions: HashMap<String, (Loc, Type)>,
}

impl Typechecker {
    pub fn new() -> Self {
        Self {
            constructors: HashMap::new(),
            types: HashSet::new(),
            functions: HashMap::new(),
        }
    }

    pub fn register_type(
        &mut self,
        name: &str,
        constructors: &[TypeConstructor],
        loc: Loc,
    ) -> Result<(), Error> {
        // Check that type name is not already in use
        if self.types.contains(name) {
            return Err(Error::TypeAlreadyDefined(loc, name.to_string()));
        }

        // Check that constructors are well-formed
        self.types.insert(name.to_string());
        for ctor in constructors {
            let ctor_type = make_constructor_type(&name, &ctor);
            // Note: we don't check the type now.
            // That happens later, see `check_all_types`.
            match self.constructors.get(&ctor.name.to_string()) {
                None => {
                    self.constructors
                        .insert(ctor.name.to_string(), (ctor.loc(), ctor_type));
                }
                Some(existing_ctor) => {
                    return Err(Error::DuplicateConstructor { existing: existing_ctor.clone(), duplicate: ctor.clone() })
                }
            }
        }
        Ok(())
    }

    pub fn register_func(
        &mut self,
        name: &str,
        source_type: &SourceType,
        loc: Loc,
    ) -> Result<(), Error> {
        // TODO: Check that function name is not already in use
        // TODO: Check that type is well-formed
        let ty = Type::from_source_type(&source_type);
        self.functions.insert(name.to_string(), (loc, ty));
        Ok(())
    }

    pub fn check_func(&self, func: &Expr, expected_type: &SourceType) -> Result<(), Error> {
        let ty = Type::from_source_type(expected_type);
        self.check_expr(&LocalVariables::new(), func, &ty)
    }

    fn check_expr(
        &self,
        local_variables: &LocalVariables<Type>,
        expr: &Expr,
        expected_type: &Type,
    ) -> Result<(), Error> {
        match expr {
            Expr::Int(loc, _) => self.assert_type_eq(expected_type, &TYPE_INT, *loc),
            Expr::Var(loc, v) => {
                let ty = self.infer_var(local_variables, v, *loc)?;
                self.assert_type_eq(expected_type, &ty, *loc)
            }
            Expr::Match {
                target,
                branches,
                loc,
                ..
            } => {
                // Infer the type of the target
                let target_type = self.infer_expr(local_variables, target)?;

                // There must be at least one branch
                if branches.is_empty() {
                    return Err(Error::EmptyMatch(*loc));
                }

                self.check_match_expr(local_variables, branches, &target_type, &expected_type)?;

                Ok(())
            }
            Expr::Func { args, body, .. } => {
                // Deconstruct expected type
                let mut func_arg_types = expected_type.func_args().into_iter();

                let mut new_locals = HashMap::new();

                // Add each arg to local variables
                for (_, arg) in args {
                    match func_arg_types.next() {
                        Some(arg_type) => {
                            new_locals.insert(arg.clone(), arg_type.clone());
                        }
                        None => {
                            todo!("what error?");
                        }
                    }
                }

                // Reconstruct remaining args into result type
                let result_type = Type::from_func_args(&func_arg_types.collect());

                // TODO: use new locals when checking body

                self.check_expr(
                    &local_variables.extend(new_locals),
                    body,
                    &result_type,
                )
            }
            Expr::App {
                head, args, loc, ..
            } => {
                // Infer type of head
                let head_type = self.infer_expr(local_variables, head)?;

                // Check that head is a function type
                match head_type {
                    Type::Func(_, _) => {},
                    _ => {
                        return Err(Error::CannotApplyNonFunction { loc: *loc, actual_type: head_type });
                    }
                }

                // Split type into args and result
                let mut head_type_args = head_type.func_args();
                // Because we know head_type is a function type, this pop_back is safe
                let head_type_result = head_type_args.pop_back().unwrap();
                let mut head_type_args = head_type_args.into_iter();

                // Check if we are given too many arguments
                if head_type_args.len() < args.len() {
                    return Err(Error::TooManyArgumentsInApplication {
                        max_number_of_arguments: head_type_args.len(),
                        actual_number_of_arguments: args.len(),
                        loc: expr.loc()
                    });
                }

                for arg in args {
                    match head_type_args.next() {
                        Some(ty) => {
                            self.check_expr(local_variables, arg, ty)?;
                        }
                        None => unreachable!()
                    }
                }

                // Reconstruct result type
                let mut head_type_args: VecDeque<_> = head_type_args.collect();
                head_type_args.push_back(head_type_result);
                let result_type = Type::from_func_args(&Vec::from(head_type_args));
                self.assert_type_eq(expected_type, &result_type, *loc)?;
                Ok(())
            }
        }
    }

    fn infer_expr(&self, local_variables: &LocalVariables<Type>, expr: &Expr) -> Result<Type, Error> {
        match expr {
            Expr::Int(_, _) => Ok(TYPE_INT),
            Expr::Var(loc, v) => self.infer_var(local_variables, v, *loc),
            Expr::Match {
                target,
                branches,
                loc,
                ..
            } => {
                // Infer the type of the target
                let target_type = self.infer_expr(local_variables, target)?;

                // There must be at least one branch
                if branches.is_empty() {
                    return Err(Error::EmptyMatch(*loc));
                }

                // Infer the return type of the first branch
                let result_type =
                    self.infer_match_branch(local_variables, &target_type, &branches[0])?;

                self.check_match_expr(local_variables, branches, &target_type, &result_type)?;

                Ok(result_type)
            }
            Expr::Func { loc, .. } => Err(Error::CannotInferTypeOfFunctions(*loc)),
            Expr::App {
                head, args, loc, ..
            } => {
                // Infer the type of the function
                let head_ty = self.infer_expr(local_variables, &head)?;

                // Deconstruct the function type
                match head_ty {
                    Type::Func(_, _) => {
                        let mut func_arg_types = head_ty.func_args().into_iter();

                        // Check each arg against the corresponding arg type
                        // There may be more arg types than args, but not vice versa
                        for arg in args {
                            match func_arg_types.next() {
                                Some(arg_type) => {
                                    self.check_expr(local_variables, arg, arg_type)?;
                                }
                                None => {
                                    todo!("what error to return here?");
                                }
                            }
                        }

                        // Construct the result type from the remaining func_args
                        Ok(Type::from_func_args(&func_arg_types.collect()))
                    }
                    _ => {
                        return Err(Error::ExpectedFunctionType {
                            loc: *loc,
                            actual_type: head_ty.clone(),
                        });
                    }
                }
            }
        }
    }

    fn check_match_expr(
        &self,
        local_variables: &LocalVariables<Type>,
        branches: &Vec<MatchBranch>,
        target_type: &Type,
        result_type: &Type,
    ) -> Result<(), Error> {
        // For each branch...
        for branch in branches {
            let new_vars = self.check_match_branch_pattern(&branch.pattern, target_type)?;
            let local_variables = local_variables.extend(new_vars);
            self.check_expr(&local_variables, &branch.rhs, result_type)?;
        }

        Ok(())
    }
    
    /// Check that `pattern` has type `expected_type` and return a map of variables bound by the
    /// pattern.
    fn check_match_branch_pattern(&self, pattern: &Pattern, expected_type: &Type) -> Result<HashMap<String, Type>, Error> {
        let mut new_vars = HashMap::new();
        match pattern {
            Pattern::Var { name, .. } => {
                new_vars.insert(name.to_string(), (*expected_type).clone());
            },
            Pattern::Int { loc, .. } => {
                self.assert_type_eq(expected_type, &TYPE_INT, *loc)?;
            }
            Pattern::Wildcard { .. } => {},
            Pattern::Constructor { name, args, loc, .. } => {
                // Check the constructor result type matches `expected_type`
                let ctor_ty = match self.constructors.get(name) {
                    None => {
                        return Err(Error::UnknownConstructor(*loc, name.to_string()));
                    }
                    Some((_, ty)) => {
                        // func_args always returns a non-empty vector, so this unwrap is safe
                        let ctor_result_type = *ty.func_args().back().unwrap();
                        self.assert_type_eq(expected_type, &ctor_result_type, *loc)?;
                        ty
                    }
                };

                // Check the constructor has the right number of args
                let ctor_ty_args = ctor_ty.func_args();
                let num_args_in_ctor_type = ctor_ty_args.len() - 1; // last elem is the result type
                if num_args_in_ctor_type != args.len() {
                    // TODO: rename to MatchBranchPatternArgNumberMismatch
                    return Err(Error::MatchBranchArgNumberMismatch {
                        loc: *loc,
                        number_of_args_in_branch: args.len(),
                        number_of_args_in_constructor_type: num_args_in_ctor_type,
                    });
                }

                // Add each pattern to the set of local variables
                for (pattern, ty) in args.iter().zip(ctor_ty_args.into_iter()) {
                    let vars = self.check_match_branch_pattern(&pattern, &ty)?;
                    new_vars.extend(vars);
                    // match pattern {
                    //     Pattern::Var { name, .. } => {
                    //         new_vars.insert(name.to_string(), ty.clone());
                    //     },
                    //     Pattern::Int { .. } => {}
                    //     Pattern::Wildcard { .. } => {},
                    //     Pattern::Constructor { .. } => {
                    //     },
                    // }
                }
            },
        }
        Ok(new_vars)
    }

    fn infer_var(
        &self,
        local_variables: &LocalVariables<Type>,
        var: &Var,
        loc: Loc,
    ) -> Result<Type, Error> {
        match var {
            Var::Local(s) => self.lookup(local_variables, s, loc),
            Var::Constructor(s) => match self.constructors.get(s) {
                Some((_, ty)) => Ok(ty.clone()),
                None => Err(Error::UnknownConstructor(loc, s.to_string())),
            },
            Var::Operator(op) => match op {
                Operator::Add | Operator::Sub | Operator::Mul => Ok(Type::Func(
                    Box::new(Type::Int),
                    Box::new(Type::Func(Box::new(Type::Int), Box::new(Type::Int))),
                )),
            },
        }
    }

    fn infer_match_branch(
        &self,
        local_variables: &LocalVariables<Type>,
        target_type: &Type,
        branch: &MatchBranch,
    ) -> Result<Type, Error> {
        match &branch.pattern {
            Pattern::Int { .. } | Pattern::Wildcard { .. } => {
                self.infer_expr(&local_variables, &branch.rhs)
            },
            Pattern::Var { .. } => todo!(),
            Pattern::Constructor { name, args, .. } => {
                // Lookup the type of the constructor and check it matches the target type.
                let ctor_ty = match self.constructors.get(name) {
                    None => {
                        return Err(Error::UnknownConstructor(
                            branch.loc(),
                            name.to_string(),
                        ));
                    }
                    Some((loc, ty)) => {
                        self.assert_type_eq(&target_type, &ty, *loc)?;
                        ty
                    }
                };

                // Check the constructor has the right number of args
                let ctor_ty_args = ctor_ty.func_args();
                let num_args_in_ctor_type = ctor_ty_args.len() - 1; // last elem is the result type
                if num_args_in_ctor_type != args.len() {
                    return Err(Error::MatchBranchArgNumberMismatch {
                        loc: branch.loc(),
                        number_of_args_in_branch: args.len(),
                        number_of_args_in_constructor_type: num_args_in_ctor_type,
                    });
                }

                // Add each pattern to the set of local variables
                let mut new_vars = HashMap::new();
                for (pattern, ty) in args.iter().zip(ctor_ty_args.into_iter()) {
                    match pattern {
                        Pattern::Var { name, .. } => {
                            new_vars.insert(name.to_string(), ty.clone());
                        },
                        Pattern::Int { .. } | Pattern::Wildcard { .. } => {},
                        Pattern::Constructor { .. } => todo!(),
                    }
                }
                let local_variables = local_variables.extend(new_vars);

                // Infer the rhs
                self.infer_expr(&local_variables, &branch.rhs)
            }
        }
    }

    fn lookup(
        &self,
        local_variables: &LocalVariables<Type>,
        name: &str,
        loc: Loc,
    ) -> Result<Type, Error> {
        match local_variables.lookup(name) {
            Some(ty) => Ok(ty.clone()),
            None => match self.functions.get(name) {
                Some((_, ty)) => Ok(ty.clone()),
                None => Err(Error::UnknownVariable(loc, name.to_string())),
            },
        }
    }

    fn assert_type_eq(&self, expected: &Type, actual: &Type, loc: Loc) -> Result<(), Error> {
        if expected == actual {
            return Ok(());
        }
        Err(Error::ExpectedType {
            loc,
            expected: expected.clone(),
            actual: actual.clone(),
        })
    }

    /// Check the well-formedness of all registered types.
    /// We do this after registering, so that circular references are allowed.
    /// If we check each type up-front, we have to register them in reverse dependency order.
    pub fn check_all_types(&self) -> Result<(), Error> {
        for (loc, ctor_type) in self.constructors.values() {
            self.check_type(ctor_type, *loc)?;
        }
        Ok(())
    }

    pub fn check_type(&self, ty: &Type, loc: Loc) -> Result<(), Error> {
        // Check that all mentioned types exist.
        match ty {
            Type::Named(n) => {
                if !self.types.contains(n) {
                    return Err(Error::UnknownType(loc, n.to_string()));
                }
            }
            Type::Func(f, x) => {
                self.check_type(f, loc)?;
                self.check_type(x, loc)?;
            }
            Type::Int => {},
            Type::App { head, args } => {
                self.check_type(head, loc)?;
                for arg in args {
                    self.check_type(arg, loc)?;
                }
            }
        }
        Ok(())
    }
}

fn make_constructor_type(type_name: &str, constructor: &TypeConstructor) -> Type {
    // Create a function type with the constructor's type as the result
    // e.g.
    // type Foo { MkFoo Int Bool Char }
    // has type
    // MkFoo : Int -> Bool -> Char -> Foo

    let mut ty = Type::Named(type_name.to_string());
    for a in constructor.arguments.iter().rev().cloned() {
        ty = Type::Func(Box::new(Type::from_source_type(&a)), Box::new(ty));
    }
    ty
}

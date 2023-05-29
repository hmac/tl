use std::collections::{HashMap, VecDeque};

use crate::ast::*;
use crate::local_variables::LocalVariables;

use tracing::debug;

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
    DuplicateConstructor {
        existing: (String, Loc, Type),
        duplicate: TypeConstructor,
    },
    CannotApplyNonFunction {
        loc: Loc,
        actual_type: Type,
    },
    TooManyArgumentsInApplication {
        loc: Loc,
        max_number_of_arguments: usize,
        actual_number_of_arguments: usize,
    },
    OccursCheck {
        loc: Loc,
        expected: Type,
        actual: Type,
    },
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
            Error::OccursCheck { loc, .. } => *loc,
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
            Error::TooManyArgumentsInApplication {
                max_number_of_arguments,
                actual_number_of_arguments,
                ..
            } => {
                write!(
                    f,
                    "this function takes {max_number_of_arguments} {}, but is given {actual_number_of_arguments}",
                    if *max_number_of_arguments > 1 { "arguments" } else { "argument" }
                )
            }
            Error::OccursCheck {
                expected, actual, ..
            } => {
                write!(
                    f,
                    "expected this to have the type {expected}, but it actually has the type {actual}. These types cannot be unified because one refers to the other."
                )
            }
        }
    }
}

type TypeVariables = HashMap<String, VarState>;

/// The state of a type variable during type checking
enum VarState {
    /// The variable is current unsolved.
    Unsolved,
    /// The variable has been solved to a type.
    Solved(Type),
    /// The variable must remain polymorphic, so cannot be solved.
    Poly,
}

pub struct Typechecker {
    // constructor name => (type name, location, constructor type)
    constructors: HashMap<String, (String, Loc, Type)>,
    // type name => type parameters
    types: HashMap<String, Vec<String>>,
    functions: HashMap<String, (Loc, Type)>,
}

impl Typechecker {
    pub fn new() -> Self {
        let mut types = HashMap::new();
        let mut constructors = HashMap::new();
        types.insert("Bool".to_string(), vec![]);
        // Insert the constructors for Bool, which is a built-in type.
        // The locations are fake.
        constructors.insert("True".to_string(), ("Bool".to_string(), (0, 0), Type::Bool));
        constructors.insert(
            "False".to_string(),
            ("Bool".to_string(), (0, 0), Type::Bool),
        );
        Self {
            constructors,
            types,
            functions: HashMap::new(),
        }
    }

    pub fn register_type(
        &mut self,
        name: &str,
        params: &Vec<String>,
        constructors: &[TypeConstructor],
        loc: Loc,
    ) -> Result<(), Error> {
        // Check that type name is not already in use
        if self.types.contains_key(name) {
            return Err(Error::TypeAlreadyDefined(loc, name.to_string()));
        }

        // Check that constructors are well-formed
        self.types.insert(name.to_string(), params.to_owned());
        for ctor in constructors {
            let ctor_type = make_constructor_type(&name, params, &ctor);
            // Note: we don't check the type now.
            // That happens later, see `check_all_types`.
            match self.constructors.get(&ctor.name.to_string()) {
                None => {
                    self.constructors.insert(
                        ctor.name.to_string(),
                        (name.to_string(), ctor.loc(), ctor_type),
                    );
                }
                Some(existing_ctor) => {
                    return Err(Error::DuplicateConstructor {
                        existing: existing_ctor.clone(),
                        duplicate: ctor.clone(),
                    })
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
        let mut type_variables = HashMap::new();
        let ty = Type::from_source_type(expected_type);
        // The type variables found here should NOT be unified with concrete types, as they
        // are part of the function's signature and so should remain polymorphic.
        // We indicate this by setting their VarState to Poly.
        for var in ty.vars() {
            type_variables.insert(var, VarState::Poly);
        }
        self.check_expr(&LocalVariables::new(), &mut type_variables, func, &ty)
    }

    /// Generate fresh names for new type variables introduced in `ty`.
    /// Type variables are collected and renamed if they conflict with an existing in-scope
    /// type variable.
    fn generate_fresh_type_variables(
        &self,
        mut ty: Type,
        existing_type_variables: &TypeVariables,
    ) -> (Type, Vec<String>) {
        let mut vars: Vec<String> = ty.vars();
        // If any of these vars conflict with an existing var, we must rename them.
        // Then we must update any occurrences of the renamed variables in the type.
        let mut substitution: HashMap<String, String> = HashMap::new();
        for var in vars.iter_mut() {
            match self.rename(var.as_str(), existing_type_variables) {
                // Variable was not renamed - nothing to do.
                None => {}
                Some(renamed) => {
                    // Variable was renamed, so we must add it to the substitution
                    substitution.insert(var.clone(), renamed.clone());
                    *var = renamed;
                }
            }
        }

        ty.rename_vars(&substitution);

        // Update our list of variables with the substituion
        vars = vars
            .into_iter()
            .map(|v| substitution.remove(&v).unwrap_or(v))
            .collect();

        (ty, vars)
    }

    // TODO: make standalone function
    fn rename(&self, var: &str, existing_type_variables: &TypeVariables) -> Option<String> {
        if !existing_type_variables.contains_key(var) {
            return None;
        }

        let mut n: usize = 0;
        loop {
            n += 1;
            let new_var = format!("{var}{n}");
            if !existing_type_variables.contains_key(&new_var) {
                return Some(new_var);
            }
        }
    }

    fn check_expr(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        expr: &Expr,
        expected_type: &Type,
    ) -> Result<(), Error> {
        debug!("check_expr({:?}, {})", expr, expected_type);
        match expr {
            Expr::Int(loc, _) => {
                self.assert_type_eq(type_variables, expected_type, &TYPE_INT, *loc)
            }
            Expr::Var(loc, v) => {
                let ty = self.infer_var(local_variables, type_variables, v, *loc)?;
                self.assert_type_eq(type_variables, expected_type, &ty, *loc)
            }
            Expr::Match {
                target,
                branches,
                loc,
                ..
            } => {
                // Infer the type of the target
                let target_type = self.infer_expr(local_variables, type_variables, target)?;

                // There must be at least one branch
                if branches.is_empty() {
                    return Err(Error::EmptyMatch(*loc));
                }

                self.check_match_expr(
                    local_variables,
                    type_variables,
                    branches,
                    &target_type,
                    &expected_type,
                )?;

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

                self.check_expr(
                    &local_variables.extend(new_locals),
                    type_variables,
                    body,
                    &result_type,
                )
            }
            Expr::App {
                head, args, loc, ..
            } => {
                // Infer type of head
                let head_type = self.infer_expr(local_variables, type_variables, head)?;

                // Check that head is a function type
                match head_type {
                    Type::Func(_, _) => {}
                    _ => {
                        return Err(Error::CannotApplyNonFunction {
                            loc: *loc,
                            actual_type: head_type,
                        });
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
                        loc: expr.loc(),
                    });
                }

                for arg in args {
                    match head_type_args.next() {
                        Some(ty) => {
                            self.check_expr(local_variables, type_variables, arg, ty)?;
                        }
                        None => unreachable!(),
                    }
                }

                // Reconstruct result type
                let mut head_type_args: VecDeque<_> = head_type_args.collect();
                head_type_args.push_back(head_type_result);
                let result_type = Type::from_func_args(&Vec::from(head_type_args));
                self.assert_type_eq(type_variables, expected_type, &result_type, *loc)?;
                Ok(())
            }
        }
    }

    fn infer_expr(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        expr: &Expr,
    ) -> Result<Type, Error> {
        match expr {
            Expr::Int(_, _) => Ok(TYPE_INT),
            Expr::Var(loc, v) => self.infer_var(local_variables, type_variables, v, *loc),
            Expr::Match {
                target,
                branches,
                loc,
                ..
            } => {
                // Infer the type of the target
                let target_type = self.infer_expr(local_variables, type_variables, target)?;

                // There must be at least one branch
                if branches.is_empty() {
                    return Err(Error::EmptyMatch(*loc));
                }

                // Infer the return type of the first branch
                let result_type = self.infer_match_branch(
                    local_variables,
                    type_variables,
                    &target_type,
                    &branches[0],
                )?;

                self.check_match_expr(
                    local_variables,
                    type_variables,
                    branches,
                    &target_type,
                    &result_type,
                )?;

                Ok(result_type)
            }
            Expr::Func { loc, .. } => Err(Error::CannotInferTypeOfFunctions(*loc)),
            Expr::App {
                head, args, loc, ..
            } => {
                // Infer the type of the function
                let head_ty = self.infer_expr(local_variables, type_variables, &head)?;

                // Deconstruct the function type
                match head_ty {
                    Type::Func(_, _) => {
                        let mut func_arg_types = head_ty.func_args().into_iter();

                        // Check each arg against the corresponding arg type
                        // There may be more arg types than args, but not vice versa
                        for arg in args {
                            match func_arg_types.next() {
                                Some(arg_type) => {
                                    self.check_expr(
                                        local_variables,
                                        type_variables,
                                        arg,
                                        arg_type,
                                    )?;
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
        type_variables: &mut TypeVariables,
        branches: &Vec<MatchBranch>,
        target_type: &Type,
        result_type: &Type,
    ) -> Result<(), Error> {
        // For each branch...
        for branch in branches {
            let new_vars =
                self.check_match_branch_pattern(type_variables, &branch.pattern, target_type)?;
            let local_variables = local_variables.extend(new_vars);
            self.check_expr(&local_variables, type_variables, &branch.rhs, result_type)?;
        }

        Ok(())
    }

    /// Check that `pattern` has type `expected_type` and return a map of variables bound by the
    /// pattern.
    fn check_match_branch_pattern(
        &self,
        type_variables: &mut TypeVariables,
        pattern: &Pattern,
        expected_type: &Type,
    ) -> Result<HashMap<String, Type>, Error> {
        let mut new_vars = HashMap::new();
        match pattern {
            Pattern::Var { name, .. } => {
                new_vars.insert(name.to_string(), (*expected_type).clone());
            }
            Pattern::Int { loc, .. } => {
                self.assert_type_eq(type_variables, expected_type, &TYPE_INT, *loc)?;
            }
            Pattern::Wildcard { .. } => {}
            Pattern::Constructor {
                name, args, loc, ..
            } => {
                // Check the constructor result type matches `expected_type`
                let ctor_ty = {
                    let ty = self.lookup_constructor(type_variables, name, *loc)?;

                    // func_args always returns a non-empty vector, so this unwrap is safe
                    let ctor_result_type = *ty.func_args().back().unwrap();
                    self.assert_type_eq(type_variables, expected_type, &ctor_result_type, *loc)?;
                    ty
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
                    let vars = self.check_match_branch_pattern(type_variables, &pattern, &ty)?;
                    new_vars.extend(vars);
                }
            }
        }
        Ok(new_vars)
    }

    fn infer_var(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        var: &Var,
        loc: Loc,
    ) -> Result<Type, Error> {
        match var {
            Var::Local(s) => self.lookup(local_variables, type_variables, s, loc),
            Var::Constructor(s) => self.lookup_constructor(type_variables, s, loc),
            Var::Operator(op) => match op {
                Operator::Add | Operator::Sub | Operator::Mul => Ok(Type::Func(
                    Box::new(Type::Int),
                    Box::new(Type::Func(Box::new(Type::Int), Box::new(Type::Int))),
                )),
                Operator::Eq => {
                    // eq : a -> a -> Bool
                    let ty = Type::Func(
                        Box::new(Type::Var("a".to_string())),
                        Box::new(Type::Func(
                            Box::new(Type::Var("a".to_string())),
                            Box::new(Type::Bool),
                        )),
                    );
                    let (ty, vars) = self.generate_fresh_type_variables(ty, type_variables);
                    for var in vars {
                        type_variables.insert(var, VarState::Unsolved);
                    }
                    Ok(ty)
                }
            },
        }
    }

    fn infer_match_branch(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        target_type: &Type,
        branch: &MatchBranch,
    ) -> Result<Type, Error> {
        match &branch.pattern {
            Pattern::Int { .. } | Pattern::Wildcard { .. } => {
                self.infer_expr(local_variables, type_variables, &branch.rhs)
            }
            Pattern::Var { .. } => todo!(),
            Pattern::Constructor { name, args, .. } => {
                // Lookup the type of the constructor and check it matches the target type.
                let ctor_ty = match self.constructors.get(name) {
                    None => {
                        return Err(Error::UnknownConstructor(branch.loc(), name.to_string()));
                    }
                    Some((_, loc, ty)) => {
                        self.assert_type_eq(type_variables, &target_type, &ty, *loc)?;
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
                        }
                        Pattern::Int { .. } | Pattern::Wildcard { .. } => {}
                        Pattern::Constructor { .. } => todo!(),
                    }
                }
                let local_variables = local_variables.extend(new_vars);

                // Infer the rhs
                self.infer_expr(&local_variables, type_variables, &branch.rhs)
            }
        }
    }

    fn lookup(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        name: &str,
        loc: Loc,
    ) -> Result<Type, Error> {
        match local_variables.lookup(name) {
            Some(ty) => Ok(ty.clone()),
            None => match self.functions.get(name) {
                Some((_, ty)) => {
                    // This function type may have type variables that we must instantiate.
                    let (ty, vars) = self.generate_fresh_type_variables(ty.clone(), type_variables);
                    for var in vars {
                        type_variables.insert(var, VarState::Unsolved);
                    }
                    Ok(ty.clone())
                }
                None => Err(Error::UnknownVariable(loc, name.to_string())),
            },
        }
    }

    fn lookup_constructor(
        &self,
        type_variables: &mut TypeVariables,
        name: &str,
        loc: Loc,
    ) -> Result<Type, Error> {
        match self.constructors.get(name) {
            None => Err(Error::UnknownConstructor(loc, name.to_string())),
            Some((_, _, ty)) => {
                // This constructor type may have type variables that we must instantiate.
                let (ty, vars) = self.generate_fresh_type_variables(ty.clone(), type_variables);
                for var in vars {
                    type_variables.insert(var, VarState::Unsolved);
                }
                Ok(ty)
            }
        }
    }

    fn assert_type_eq<'a>(
        &self,
        type_variables: &mut TypeVariables,
        expected: &'a Type,
        actual: &'a Type,
        loc: Loc,
    ) -> Result<(), Error> {
        debug!("assert_type_eq({}, {})", &expected, &actual);
        if expected == actual {
            return Ok(());
        }

        // If the application heads match, try to equate their arguments
        match (expected, actual) {
            (Type::Var(expected_var), Type::Var(actual_var)) => {
                self.assert_var_eq(type_variables, expected_var, actual_var, loc)
            }
            (Type::Var(expected_var), actual) => {
                self.try_solve_type_var(type_variables, expected_var, actual, loc, false)?;
                Ok(())
            }
            (expected, Type::Var(actual_var)) => {
                // TODO: since expected and actual are swapped here, we get an error message with
                // swapped "expected" and "actual" fields. Fix this.
                self.try_solve_type_var(type_variables, actual_var, expected, loc, true)?;
                Ok(())
            }
            (Type::Int, _) | (_, Type::Int) | (Type::Bool, _) | (_, Type::Bool) => {
                Err(Error::ExpectedType {
                    loc,
                    expected: expected.clone(),
                    actual: actual.clone(),
                })
            }
            (Type::Named(_), _) => Err(Error::ExpectedType {
                loc,
                expected: expected.clone(),
                actual: actual.clone(),
            }),
            (_, Type::Named(_)) => Err(Error::ExpectedType {
                loc,
                expected: expected.clone(),
                actual: actual.clone(),
            }),
            (
                Type::App {
                    head: head_expected,
                    args: args_expected,
                },
                Type::App {
                    head: head_actual,
                    args: args_actual,
                },
            ) => {
                self.assert_type_eq(type_variables, head_expected, head_actual, loc)?;

                assert_eq!(args_expected.len(), args_actual.len());

                for (arg_expected, arg_actual) in args_expected.iter().zip(args_actual.iter()) {
                    self.assert_type_eq(type_variables, arg_expected, arg_actual, loc)?;
                }

                Ok(())
            }
            (Type::App { .. }, _) => Err(Error::ExpectedType {
                loc,
                expected: expected.clone(),
                actual: actual.clone(),
            }),
            (_, Type::App { .. }) => Err(Error::ExpectedType {
                loc,
                expected: expected.clone(),
                actual: actual.clone(),
            }),
            (Type::Func(f_expected, x_expected), Type::Func(f_actual, x_actual)) => {
                self.assert_type_eq(type_variables, f_expected, f_actual, loc)?;
                self.assert_type_eq(type_variables, x_expected, x_actual, loc)?;
                Ok(())
            }
        }
    }

    fn assert_var_eq(
        &self,
        type_variables: &mut TypeVariables,
        expected: &str,
        actual: &str,
        loc: Loc,
    ) -> Result<(), Error> {
        debug!("assert_var_eq({}, {})", expected, actual);
        let expected_var = type_variables.get(expected);
        match expected_var {
            Some(VarState::Unsolved) => {
                match type_variables.get_mut(actual) {
                    Some(actual_var) => {
                        match actual_var {
                            VarState::Unsolved => {
                                // expected and actual are both unsolved,
                                // so set them equal to each other
                                debug!("solve: {} = {}", expected, actual);
                                *actual_var = VarState::Solved(Type::Var(expected.to_string()));
                                Ok(())
                            }
                            VarState::Solved(actual) => {
                                // actual is already solved, so recurse
                                let actual = actual.clone();
                                self.try_solve_type_var(
                                    type_variables,
                                    expected,
                                    &actual,
                                    loc,
                                    false,
                                )?;
                                Ok(())
                            }
                            VarState::Poly => {
                                self.assert_var_eq(type_variables, actual, expected, loc)
                            }
                        }
                    }
                    None => todo!(),
                }
            }
            Some(VarState::Solved(expected)) => {
                // expected is solved to some type, so recurse
                let expected = expected.clone();
                self.try_solve_type_var(type_variables, actual, &expected, loc, false)?;
                Ok(())
            }
            Some(VarState::Poly) => match type_variables.get_mut(actual) {
                Some(actual_var) => match actual_var {
                    VarState::Solved(Type::Var(actual)) if actual == expected => Ok(()),
                    VarState::Poly | VarState::Solved(_) => Err(Error::ExpectedType {
                        loc,
                        actual: Type::Var(expected.to_string()),
                        expected: Type::Var(actual.to_string()),
                    }),
                    VarState::Unsolved => {
                        *actual_var = VarState::Solved(Type::Var(expected.to_string()));
                        Ok(())
                    }
                },
                _ => self.assert_var_eq(type_variables, actual, expected, loc),
            },
            None => todo!(),
        }
    }

    /// Returns true if it has solved the type variable.
    fn try_solve_type_var(
        &self,
        type_variables: &mut TypeVariables,
        expected: &str,
        actual: &Type,
        loc: Loc,
        swapped: bool,
    ) -> Result<bool, Error> {
        debug!("try_solve_type_var({}, {})", &expected, &actual);

        // First, lookup expected to see if we've already solved it.
        if let Some(VarState::Solved(t)) = type_variables.get(expected) {
            let t = t.clone();
            self.assert_type_eq(type_variables, &t, actual, loc)?;
            return Ok(false);
        }

        if let Type::Var(actual) = actual {
            if expected == actual {
                return Ok(false);
            }
        }

        if actual.vars().contains(&expected.to_string()) {
            return Err(Error::OccursCheck {
                loc,
                expected: Type::Var(expected.to_string()),
                actual: actual.clone(),
            });
        }

        debug!("solve: {} = {}", &expected, &actual);
        match type_variables.get_mut(expected) {
            None => {
                unreachable!();
            }
            Some(t) => {
                match t {
                    VarState::Unsolved => {
                        *t = VarState::Solved((*actual).clone());
                        Ok(true)
                    }
                    VarState::Solved(t) => {
                        debug!("lookup: {} = {}", &expected, &t);
                        if t == actual {
                            Ok(true)
                        } else {
                            if swapped {
                                Err(Error::ExpectedType {
                                    loc,
                                    expected: actual.clone(),
                                    actual: t.clone(),
                                })
                            } else {
                                Err(Error::ExpectedType {
                                    loc,
                                    expected: t.clone(),
                                    actual: actual.clone(),
                                })
                            }
                        }
                    }
                    VarState::Poly => {
                        // Expected type is polymorphic, so cannot be solved.
                        // The actual type could be solved to = expected type, but we may have
                        // already tried this? need to check.
                        if swapped {
                            Err(Error::ExpectedType {
                                loc,
                                actual: Type::Var(expected.to_string()),
                                expected: actual.clone(),
                            })
                        } else {
                            Err(Error::ExpectedType {
                                loc,
                                expected: Type::Var(expected.to_string()),
                                actual: actual.clone(),
                            })
                        }
                    }
                }
            }
        }
    }

    /// Check the well-formedness of all registered types.
    /// We do this after registering, so that circular references are allowed.
    /// If we check each type up-front, we have to register them in reverse dependency order.
    pub fn check_all_types(&self) -> Result<(), Error> {
        for (type_name, loc, ctor_type) in self.constructors.values() {
            match self.types.get(type_name) {
                Some(type_params) => {
                    self.check_type(ctor_type, *loc, type_params)?;
                }
                None => {
                    return Err(Error::UnknownType(*loc, type_name.to_string()));
                }
            }
        }
        Ok(())
    }

    pub fn check_type(&self, ty: &Type, loc: Loc, vars_in_scope: &[String]) -> Result<(), Error> {
        // Check that all mentioned types exist.
        match ty {
            Type::Named(n) => {
                if !self.types.contains_key(n) {
                    return Err(Error::UnknownType(loc, n.to_string()));
                }
            }
            Type::Func(f, x) => {
                self.check_type(f, loc, vars_in_scope)?;
                self.check_type(x, loc, vars_in_scope)?;
            }
            Type::Int | Type::Bool => {}
            Type::App { head, args } => {
                self.check_type(head, loc, vars_in_scope)?;
                for arg in args {
                    self.check_type(arg, loc, vars_in_scope)?;
                }
            }
            Type::Var(v) => {
                if !vars_in_scope.contains(v) {
                    return Err(Error::UnknownVariable(loc, v.to_string()));
                }
            }
        }
        Ok(())
    }
}

fn make_constructor_type(
    type_name: &str,
    params: &Vec<String>,
    constructor: &TypeConstructor,
) -> Type {
    // Create a function type with the constructor's type as the result
    // e.g.
    // type Foo { MkFoo Int Bool Char }
    // has type
    // MkFoo : Int -> Bool -> Char -> Foo

    let mut ty = Type::Named(type_name.to_string());

    if !params.is_empty() {
        let args = params.iter().map(|p| Type::Var(p.to_string())).collect();
        ty = Type::App {
            head: Box::new(ty),
            args,
        };
    }

    for a in constructor.arguments.iter().rev().cloned() {
        ty = Type::Func(Box::new(Type::from_source_type(&a)), Box::new(ty));
    }
    ty
}

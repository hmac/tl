use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};

use crate::ast::*;
use crate::local_variables::LocalVariables;

use tracing::debug;

const TYPE_INT: Type = Type::Int;
const TYPE_STRING: Type = Type::Str;
const TYPE_CHAR: Type = Type::Char;

#[derive(Debug)]
pub enum Error {
    TypeAlreadyDefined(Loc, String),
    UnknownType(Loc, GlobalName),
    UnknownVariable(Loc, String),
    UnknownConstructor(Loc, String),
    EmptyMatch(Loc),
    ExpectedType {
        loc: Loc,
        expected: Type,
        actual: Type,
    },
    CaseBranchArgNumberMismatch {
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
        existing: (GlobalName, Loc, Type),
        duplicate: TypeConstructor,
    },
    CannotApplyNonFunction {
        loc: Loc,
        actual_type: Type,
    },
    TooManyArgumentsInFunction {
        loc: Loc,
        expected_type: Type,
        expected_number_of_arguments: usize,
        actual_number_of_arguments: usize,
    },
    OccursCheck {
        loc: Loc,
        expected: Type,
        actual: Type,
    },
    MissingCasePattern {
        loc: Loc,
        // Currently we can only report missing top-level patterns
        constructor: String,
    },
    TupleUnexpectedNumberOfElements {
        loc: Loc,
        expected_number: usize,
        actual_number: usize,
    },
    ExpectedTupleType {
        loc: Loc,
        actual_type: Type,
    },
    MissingImport {
        loc: (usize, usize),
        namespace: String,
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
            Error::CaseBranchArgNumberMismatch { loc, .. } => *loc,
            Error::CannotInferTypeOfFunctions(loc) => *loc,
            Error::ExpectedFunctionType { loc, .. } => *loc,
            Error::DuplicateConstructor { duplicate, .. } => duplicate.loc,
            Error::CannotApplyNonFunction { loc, .. } => *loc,
            Error::TooManyArgumentsInFunction { loc, .. } => *loc,
            Error::OccursCheck { loc, .. } => *loc,
            Error::MissingCasePattern { loc, .. } => *loc,
            Error::TupleUnexpectedNumberOfElements { loc, .. } => *loc,
            Error::ExpectedTupleType { loc, .. } => *loc,
            Error::MissingImport { loc, .. } => *loc,
        }
    }
}

impl Error {
    pub fn with_path<'a>(&'a self, path: Option<&'a Path>) -> ErrorWithPath<'a> {
        ErrorWithPath { error: self, path }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.with_path(None).fmt(f)
    }
}

pub struct ErrorWithPath<'a> {
    error: &'a Error,
    path: Option<&'a Path>,
}

impl HasLoc for ErrorWithPath<'_> {
    fn loc(&self) -> Loc {
        self.error.loc()
    }
}

impl std::fmt::Display for ErrorWithPath<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.error {
            Error::TypeAlreadyDefined(_, ty) => {
                write!(f, "the type '{ty}' has already been defined elsewhere")
            }
            Error::UnknownType(_, ty) => {
                write!(
                    f,
                    "unknown type '{}'",
                    match self.path {
                        Some(path) => ty.display_name_relative_to_path(path),
                        None => ty.to_string(),
                    }
                )
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
                write!(
                    f,
                    "expected this to have the type {} but it actually has the type {}",
                    expected.with_path(self.path),
                    actual.with_path(self.path)
                )
            }
            Error::CaseBranchArgNumberMismatch {
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
                    "expected to have a function type, but its actual type is {}",
                    actual_type.with_path(self.path)
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
                    "this expression cannot be applied as a function, because it has type {}",
                    actual_type.with_path(self.path)
                )
            }
            Error::TooManyArgumentsInFunction {
                expected_number_of_arguments,
                actual_number_of_arguments,
                expected_type,
                ..
            } => {
                fn pluralise(i: usize) -> &'static str {
                    if i > 1 {
                        "arguments"
                    } else {
                        "argument"
                    }
                }
                write!(
                    f,
                    "this function takes {actual_number_of_arguments} {}, but its type ({}) has only {expected_number_of_arguments} {}",
                    pluralise(*actual_number_of_arguments),
                    expected_type.with_path(self.path),
                    pluralise(*expected_number_of_arguments)
                )
            }
            Error::OccursCheck {
                expected, actual, ..
            } => {
                write!(
                    f,
                    "expected this to have the type {} but it actually has the type {}. These types cannot be unified because one refers to the other.",
                    expected.with_path(self.path),
                    actual.with_path(self.path)
                )
            }
            Error::MissingCasePattern { constructor, .. } => {
                write!(
                    f,
                    "the constructor {constructor} is not covered by this case expression"
                )
            }
            Error::TupleUnexpectedNumberOfElements {
                expected_number,
                actual_number,
                ..
            } => {
                write!(
                    f,
                    "expected a tuple with {expected_number} elements, but found a tuple with {actual_number} elements"
                )
            }
            Error::ExpectedTupleType { actual_type, .. } => {
                write!(
                    f,
                    "expected this to have a tuple type, but its actual type is {}",
                    actual_type.with_path(self.path)
                )
            }
            Error::MissingImport { namespace, .. } => {
                write!(f, "this file does not import {namespace}")
            }
        }
    }
}

type TypeVariables = HashMap<String, VarState>;

/// The state of a type variable during type checking
#[derive(Debug)]
enum VarState {
    /// The variable is current unsolved.
    Unsolved,
    /// The variable has been solved to a type.
    Solved(Type),
    /// The variable must remain polymorphic, so cannot be solved.
    Poly,
}

/// Maps file paths to their imports, which is a map from import name to imported file path
#[derive(Debug, Clone)]
pub struct Imports {
    inner: HashMap<PathBuf, HashMap<String, PathBuf>>,
}

impl Imports {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Lookup a name relative to the given path.
    /// If namespace is `None`, assume the name is relative to the current module.
    pub fn lookup(
        &self,
        loc: Loc,
        path: &Path,
        ns: &Option<Namespace>,
        name: &str,
    ) -> Result<GlobalName, Error> {
        match ns {
            None => Ok(GlobalName::named(path, name)),
            Some(ns) => self
                .inner
                .get(path)
                .unwrap()
                .get(ns.as_str())
                .map(|import_path| GlobalName::named(import_path, name))
                .ok_or(Error::MissingImport {
                    loc,
                    namespace: ns.to_string(),
                }),
        }
    }

    pub fn insert(&mut self, path: &Path, imports: HashMap<String, PathBuf>) {
        self.inner.insert(path.to_path_buf(), imports);
    }
}

pub struct Typechecker {
    // constructor name => (type name, location, constructor type)
    constructors: HashMap<GlobalName, (GlobalName, Loc, Type)>,
    // type name => type parameters
    types: HashMap<GlobalName, Vec<String>>,
    functions: HashMap<GlobalName, (Loc, Type)>,
    pub imports: Imports,
}

impl Typechecker {
    pub fn new() -> Self {
        let mut types = HashMap::new();
        let mut constructors = HashMap::new();
        types.insert(GlobalName::builtin("List"), vec!["a".to_string()]);

        types.insert(GlobalName::builtin("Bool"), vec![]);
        // Insert the constructors for Bool, which is a built-in type.
        // The locations are fake.
        constructors.insert(
            GlobalName::builtin("True"),
            (GlobalName::builtin("Bool"), (0, 0), Type::Bool),
        );
        constructors.insert(
            GlobalName::builtin("False"),
            (GlobalName::builtin("Bool"), (0, 0), Type::Bool),
        );

        Self {
            constructors,
            types,
            functions: HashMap::new(),
            imports: Imports::new(),
        }
    }

    pub fn register_type(
        &mut self,
        path: &Path,
        name: &str,
        params: &Vec<String>,
        constructors: &[TypeConstructor],
        loc: Loc,
    ) -> Result<(), Error> {
        let type_name = GlobalName::named(path, name);

        // Check that type name is not already in use
        if self.types.contains_key(&type_name) {
            return Err(Error::TypeAlreadyDefined(loc, name.to_string()));
        }

        // Check that constructors are well-formed
        self.types.insert(type_name.clone(), params.to_owned());
        for ctor in constructors {
            let ctor_type = self.make_constructor_type(loc, path, None, &name, params, &ctor)?;
            let ctor_name = GlobalName::named(path, &ctor.name);
            // Note: we don't check the type now.
            // That happens later, see `check_all_types`.
            match self.constructors.get(&ctor_name) {
                None => {
                    self.constructors
                        .insert(ctor_name, (type_name.clone(), ctor.loc(), ctor_type));
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
        path: &Path,
        name: &str,
        source_type: &SourceType,
        loc: Loc,
    ) -> Result<(), Error> {
        // TODO: Check that function name is not already in use
        // TODO: Check that type is well-formed
        let ty = self.type_from_source_type(path, &source_type)?;
        self.check_type(path, &ty, source_type.loc(), &ty.vars())?;
        self.functions
            .insert(GlobalName::named(path, name), (loc, ty));
        Ok(())
    }

    pub fn check_func(
        &self,
        path: &Path,
        func: &Expr,
        expected_type: &SourceType,
    ) -> Result<(), Error> {
        let mut type_variables = HashMap::new();
        let ty = self.type_from_source_type(path, expected_type)?;
        // The type variables found here should NOT be unified with concrete types, as they
        // are part of the function's signature and so should remain polymorphic.
        // We indicate this by setting their VarState to Poly.
        for var in ty.vars() {
            type_variables.insert(var, VarState::Poly);
        }
        self.check_expr(&LocalVariables::new(), &mut type_variables, path, func, &ty)
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
        path: &Path,
        expr: &Expr,
        expected_type: &Type,
    ) -> Result<(), Error> {
        debug!("check_expr({:?}, {})", expr, expected_type);
        match expr {
            Expr::Int(loc, _) => {
                self.assert_type_eq(type_variables, expected_type, &TYPE_INT, *loc)
            }
            Expr::Str(loc, _) => {
                self.assert_type_eq(type_variables, expected_type, &TYPE_STRING, *loc)
            }
            Expr::Char(loc, _) => {
                self.assert_type_eq(type_variables, expected_type, &TYPE_CHAR, *loc)
            }
            Expr::Var(loc, v) => {
                let ty = self.infer_var(local_variables, type_variables, path, v, *loc)?;
                self.assert_type_eq(type_variables, expected_type, &ty, *loc)
            }
            Expr::Tuple { loc, elems } => match expected_type {
                Type::Tuple(expected_elem_types) => {
                    if elems.len() != expected_elem_types.len() {
                        return Err(Error::TupleUnexpectedNumberOfElements {
                            loc: *loc,
                            expected_number: expected_elem_types.len(),
                            actual_number: elems.len(),
                        });
                    }
                    for (e, t) in elems.iter().zip(expected_elem_types.iter()) {
                        self.check_expr(local_variables, type_variables, path, e, t)?;
                    }
                    Ok(())
                }
                _ => {
                    // For the tuple to typecheck, this type must unify to some tuple type
                    // (a, b, c, ...) with the number of element types matching the number of
                    // elements in the tuple.
                    // So we construct a new tuple type (t1, t2, t3, ...) with fresh type variables
                    // and unify it with the expected type.
                    let mut new_vars = vec![];
                    for e in elems {
                        let var = self.make_fresh_var(type_variables);
                        self.check_expr(local_variables, type_variables, path, e, &var)?;
                        new_vars.push(var);
                    }
                    let ty = Type::Tuple(new_vars);
                    self.assert_type_eq(type_variables, expected_type, &ty, *loc)
                }
            },
            Expr::List { loc, elems, tail } => {
                // Construct a fresh `List a` type, and unify it with the expected type.
                let elem_type = self.make_fresh_var(type_variables);
                let list_type = self.make_list_type(elem_type.clone());
                self.assert_type_eq(type_variables, expected_type, &list_type, *loc)?;
                // Check that the list elements have type `a`
                for elem in elems {
                    self.check_expr(local_variables, type_variables, path, elem, &elem_type)?;
                }
                // If present, check that the tail has type `List a`
                if let Some(tail) = tail {
                    self.check_expr(local_variables, type_variables, path, tail, &list_type)?;
                }
                Ok(())
            }
            Expr::Case {
                target,
                branches,
                loc,
                ..
            } => {
                // Infer the type of the target
                let target_type = self.infer_expr(local_variables, type_variables, path, target)?;

                // There must be at least one branch
                if branches.is_empty() {
                    return Err(Error::EmptyMatch(*loc));
                }

                // check that the branches are exhaustive.
                self.check_case_is_exhaustive(
                    *loc,
                    branches.iter().map(|b| &b.pattern),
                    &target_type,
                )?;

                self.check_match_expr(
                    local_variables,
                    type_variables,
                    path,
                    branches,
                    &target_type,
                    &expected_type,
                )?;

                Ok(())
            }
            Expr::Func {
                args, body, loc, ..
            } => {
                // Deconstruct expected type
                let mut func_arg_types = expected_type.func_args().into_iter();

                let mut new_locals = HashMap::new();

                if args.len() > func_arg_types.len() {
                    return Err(Error::TooManyArgumentsInFunction {
                        expected_number_of_arguments: func_arg_types.len(),
                        expected_type: expected_type.clone(),
                        actual_number_of_arguments: args.len(),
                        loc: *loc,
                    });
                }

                // Add each arg to local variables
                for (_, arg) in args {
                    new_locals.insert(arg.clone(), func_arg_types.next().unwrap().clone());
                }

                // TODO: if there are more expr args than type args,
                // currently we will crash.
                // e.g. in f : Int -> Int { x y z -> 1 }

                // Reconstruct remaining args into result type
                let result_type = Type::from_func_args(&func_arg_types.collect());

                self.check_expr(
                    &local_variables.extend(new_locals),
                    type_variables,
                    path,
                    body,
                    &result_type,
                )
            }
            Expr::App {
                head, args, loc, ..
            } => {
                // Infer type of head
                let head_type = self.infer_expr(local_variables, type_variables, path, head)?;

                // Check that head is a function type
                let head_type = match head_type {
                    Type::Func(_, _) => head_type,
                    Type::Var(ref v) => {
                        // Generate new vars a, b and unify v with a -> b
                        let domain = self.make_fresh_var(type_variables);
                        let range = self.make_fresh_var(type_variables);
                        let func_type = Type::Func(Box::new(domain), Box::new(range));
                        self.assert_type_eq(type_variables, expected_type, &func_type, *loc)?;
                        match type_variables.get_mut(v) {
                            Some(state) => {
                                *state = VarState::Solved(func_type.clone());
                            }
                            None => unreachable!(),
                        }
                        func_type
                    }
                    _ => {
                        return Err(Error::CannotApplyNonFunction {
                            loc: *loc,
                            actual_type: head_type,
                        });
                    }
                };

                // Split type into args and result
                let mut head_type_args = head_type.func_args();
                // Because we know head_type is a function type, this pop_back is safe
                let head_type_result = head_type_args.pop_back().unwrap();

                // There are three cases to consider:
                // 1. args.len() == head_type_args.len(). We have a fully saturated function
                //    application. This is the simple case.
                // 2. args.len() < head_type_args.len(). We have a partially saturated application.
                //    The type of the expression will be some suffix of the function's type.
                // 3. args.len() > head_type_args.len(). We have more arguments than the function's
                //    type specifies. Either the function returns another function which is then
                //    applied, or the expression is ill-typed.

                use std::cmp::Ordering;
                match args.len().cmp(&head_type_args.len()) {
                    Ordering::Equal | Ordering::Less => self.check_app_fewer_or_exact_args(
                        local_variables,
                        type_variables,
                        path,
                        head_type_args,
                        head_type_result,
                        args,
                        expected_type,
                        *loc,
                    ),
                    Ordering::Greater => self.check_app_more_args(
                        local_variables,
                        type_variables,
                        path,
                        head_type_args,
                        head_type_result,
                        args,
                        expected_type,
                        *loc,
                    ),
                }
            }
            Expr::Let { bindings, body, .. } => {
                let mut new_locals = HashMap::new();
                // Check each binding, and add to local variables
                // If binding has a type, check it. Otherwise infer.
                for LetBinding {
                    name,
                    value,
                    r#type,
                    ..
                } in bindings
                {
                    let ty = if let Some(source_type) = r#type {
                        let ty = self.type_from_source_type(path, &source_type)?;
                        // Type variables in let bindings are treated similarly to those in
                        // function signatures: they should not be unified.
                        for var in ty.vars() {
                            type_variables.insert(var, VarState::Poly);
                        }
                        // TODO: check type is well formed
                        self.check_expr(
                            &local_variables.extend(new_locals.clone()),
                            type_variables,
                            path,
                            &value,
                            &ty,
                        )?;
                        ty
                    } else {
                        self.infer_expr(
                            &local_variables.extend(new_locals.clone()),
                            type_variables,
                            path,
                            &value,
                        )?
                    };
                    new_locals.insert(name.to_string(), ty);
                }
                // Check the body
                self.check_expr(
                    &local_variables.extend(new_locals),
                    type_variables,
                    path,
                    &body,
                    expected_type,
                )
            }
        }
    }

    /// Check a function application, where there are fewer arguments than parameters in the
    /// function's type, or exactly the right number of arguments.
    fn check_app_fewer_or_exact_args(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        path: &Path,
        head_type_args: VecDeque<&Type>,
        head_type_result: &Type,
        args: &[Expr],
        expected_type: &Type,
        loc: Loc,
    ) -> Result<(), Error> {
        assert!(args.len() <= head_type_args.len());

        let mut head_type_args = head_type_args.into_iter();
        for arg in args {
            self.check_expr(
                local_variables,
                type_variables,
                path,
                arg,
                head_type_args.next().unwrap(),
            )?;
        }

        // Reconstruct result type
        let mut head_type_args: VecDeque<_> = head_type_args.collect();
        head_type_args.push_back(head_type_result);
        let result_type = Type::from_func_args(&Vec::from(head_type_args));
        self.assert_type_eq(type_variables, expected_type, &result_type, loc)?;
        Ok(())
    }

    fn check_app_more_args(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        path: &Path,
        head_type_args: VecDeque<&Type>,
        head_type_result: &Type,
        args: &[Expr],
        expected_type: &Type,
        loc: Loc,
    ) -> Result<(), Error> {
        // We have more arguments than in the function's type.
        // We must infer the type of each argument, and then construct the type
        // t = arg1type -> arg2type -> ... -> resulttype
        // and assert_type_eq(t, expected_type)
        // but we also need to check the function's type matches this, too.

        // if we have some head_type_args then we can check their corresponding arguments.
        // after that we have to infer the remaining arguments.

        // Check the args we have types for
        let mut args = args.into_iter();
        let mut last_arg_loc: Option<Loc> = None; // used to calculate locations later.
        for type_arg in head_type_args.iter() {
            match args.next() {
                Some(arg) => {
                    self.check_expr(local_variables, type_variables, path, arg, type_arg)?;
                    last_arg_loc = Some(arg.loc());
                }
                None => {
                    unreachable!();
                }
            }
        }

        // Now args holds the remaining args. We must infer each one.
        let mut remaining_arg_types = vec![];
        for arg in args {
            remaining_arg_types.push(self.infer_expr(
                local_variables,
                type_variables,
                path,
                arg,
            )?);
        }

        // We're checking that the return type of the function matches the type
        // we would expect given the types of the remaining arguments and the overall expected type
        // of the application.
        //
        // For example:
        //
        // f a b c d : T
        // ^ ^^^ ^^^
        // |  |   |
        // |  |   remaining args
        // |  |
        // |  args mentioned in type
        // |
        // f : A -> B -> z
        //
        // we construct the type C -> D -> T and unify it with z.
        //
        // If there's an error here, we want the location to be helpful.
        // We're talking about the type of the application "f a b", so the
        // location should start at f and end at b.

        // TODO: the errors generated here could be improved. See
        // fixtures/type_errors/too_many_args_in_application.tl

        let mut actual_function_result_type = expected_type.clone();
        for arg_type in remaining_arg_types.iter().rev() {
            actual_function_result_type = Type::Func(
                Box::new(arg_type.clone()),
                Box::new(actual_function_result_type),
            );
        }

        self.assert_type_eq(
            type_variables,
            &actual_function_result_type,
            head_type_result,
            (loc.0, last_arg_loc.unwrap_or(loc).1),
        )?;
        Ok(())
    }

    fn infer_expr(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        path: &Path,
        expr: &Expr,
    ) -> Result<Type, Error> {
        match expr {
            Expr::Int(_, _) => Ok(TYPE_INT),
            Expr::Str(_, _) => Ok(TYPE_STRING),
            Expr::Char(_, _) => Ok(TYPE_STRING),
            Expr::Var(loc, v) => self.infer_var(local_variables, type_variables, path, v, *loc),
            Expr::Tuple { elems, .. } => {
                let mut elem_types = vec![];
                for e in elems {
                    elem_types.push(self.infer_expr(local_variables, type_variables, path, e)?);
                }
                Ok(Type::Tuple(elem_types))
            }
            Expr::List { elems, tail, .. } => {
                // If the list is empty, generate a fresh type variable `a` and return `List a`.
                match elems.split_first() {
                    None => {
                        let list_type = self.make_fresh_list_type(type_variables);
                        // If present, check the tail
                        if let Some(tail) = tail {
                            self.check_expr(
                                local_variables,
                                type_variables,
                                path,
                                tail,
                                &list_type,
                            )?;
                        }
                        Ok(list_type)
                    }
                    Some((first, rest)) => {
                        // Infer the first element
                        // Check that the remaining elements have the same type
                        let ty = self.infer_expr(local_variables, type_variables, path, first)?;
                        for elem in rest {
                            self.check_expr(local_variables, type_variables, path, elem, &ty)?;
                        }
                        // If it exists, check that the tail has the type `List a`
                        let list_type = self.make_list_type(ty);
                        if let Some(tail) = tail {
                            self.check_expr(
                                local_variables,
                                type_variables,
                                path,
                                tail,
                                &list_type,
                            )?;
                        }
                        Ok(list_type)
                    }
                }
            }
            Expr::Case {
                target,
                branches,
                loc,
                ..
            } => {
                // Infer the type of the target
                let target_type = self.infer_expr(local_variables, type_variables, path, target)?;

                // There must be at least one branch
                if branches.is_empty() {
                    return Err(Error::EmptyMatch(*loc));
                }

                // check that the branches are exhaustive.
                self.check_case_is_exhaustive(
                    *loc,
                    branches.iter().map(|b| &b.pattern),
                    &target_type,
                )?;

                // Infer the return type of the first branch
                let result_type = self.infer_match_branch(
                    local_variables,
                    type_variables,
                    path,
                    &target_type,
                    &branches[0],
                )?;

                self.check_match_expr(
                    local_variables,
                    type_variables,
                    path,
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
                let head_ty = self.infer_expr(local_variables, type_variables, path, &head)?;

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
                                        path,
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
                    _ => Err(Error::ExpectedFunctionType {
                        loc: *loc,
                        actual_type: head_ty.clone(),
                    }),
                }
            }
            Expr::Let { bindings, body, .. } => {
                let mut new_locals = HashMap::new();
                // Infer each binding, and add to local variables
                for LetBinding { name, value, .. } in bindings {
                    let ty = self.infer_expr(
                        &local_variables.extend(new_locals.clone()),
                        type_variables,
                        path,
                        &value,
                    )?;
                    new_locals.insert(name.to_string(), ty);
                }
                // Infer the body
                self.infer_expr(
                    &local_variables.extend(new_locals),
                    type_variables,
                    path,
                    &body,
                )
            }
        }
    }

    fn check_match_expr(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        path: &Path,
        branches: &Vec<CaseBranch>,
        target_type: &Type,
        result_type: &Type,
    ) -> Result<(), Error> {
        // For each branch...
        for branch in branches {
            let new_vars = self.check_match_branch_pattern(
                type_variables,
                path,
                &branch.pattern,
                target_type,
            )?;
            let local_variables = local_variables.extend(new_vars);
            self.check_expr(
                &local_variables,
                type_variables,
                path,
                &branch.rhs,
                result_type,
            )?;
        }

        Ok(())
    }

    /// Check that `pattern` has type `expected_type` and return a map of variables bound by the
    /// pattern.
    fn check_match_branch_pattern(
        &self,
        type_variables: &mut TypeVariables,
        path: &Path,
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
            Pattern::ListNil { loc, .. } => {
                let var = self.make_fresh_var(type_variables);
                let list_type = self.make_list_type(var);
                self.assert_type_eq(type_variables, expected_type, &list_type, *loc)?;
            }
            Pattern::ListCons { loc, elems, tail } => {
                // Check that the expected type is List a for some a
                let var = self.make_fresh_var(type_variables);
                let list_type = self.make_list_type(var.clone());
                self.assert_type_eq(type_variables, expected_type, &list_type, *loc)?;

                // Check that each pattern has type a
                for e in elems {
                    new_vars.extend(self.check_match_branch_pattern(
                        type_variables,
                        path,
                        e,
                        &var,
                    )?);
                }
                // Check that the tail, if present, has type List a
                if let Some(tail) = tail {
                    new_vars.extend(self.check_match_branch_pattern(
                        type_variables,
                        path,
                        tail,
                        &list_type,
                    )?);
                }
            }
            Pattern::Tuple { loc, elems } => {
                // The expected type must be a tuple type with the same number of elements
                let mut ty_vars = vec![];
                for p in elems {
                    let var = self.make_fresh_var(type_variables);
                    new_vars.extend(self.check_match_branch_pattern(
                        type_variables,
                        path,
                        p,
                        &var,
                    )?);
                    ty_vars.push(var);
                }
                let tuple_type = Type::Tuple(ty_vars.clone());
                self.assert_type_eq(type_variables, expected_type, &tuple_type, *loc)?;
            }
            Pattern::Wildcard { .. } => {}
            Pattern::Constructor {
                namespace,
                name,
                args,
                loc,
                ..
            } => {
                // Check the constructor result type matches `expected_type`
                let ctor_ty = {
                    // We currently assume that the constructor is defined in the same file (or is
                    // a builtin)
                    let ctor_name = match name.as_str() {
                        "True" | "False" => GlobalName::builtin(name),
                        _ => self.imports.lookup(*loc, path, namespace, name)?,
                    };

                    let ty = self.lookup_constructor(type_variables, &ctor_name, *loc)?;

                    // func_args always returns a non-empty vector, so this unwrap is safe
                    let ctor_result_type = *ty.func_args().back().unwrap();
                    self.assert_type_eq(type_variables, expected_type, &ctor_result_type, *loc)?;
                    ty
                };

                // Check the constructor has the right number of args
                let ctor_ty_args = ctor_ty.func_args();
                let num_args_in_ctor_type = ctor_ty_args.len() - 1; // last elem is the result type
                if num_args_in_ctor_type != args.len() {
                    // TODO: rename to CaseBranchPatternArgNumberMismatch
                    return Err(Error::CaseBranchArgNumberMismatch {
                        loc: *loc,
                        number_of_args_in_branch: args.len(),
                        number_of_args_in_constructor_type: num_args_in_ctor_type,
                    });
                }

                // Add each pattern to the set of local variables
                for (pattern, ty) in args.iter().zip(ctor_ty_args.into_iter()) {
                    let vars =
                        self.check_match_branch_pattern(type_variables, path, &pattern, &ty)?;
                    new_vars.extend(vars);
                }
            }
        }
        Ok(new_vars)
    }

    fn check_case_is_exhaustive<'a, I: Iterator<Item = &'a Pattern>>(
        &self,
        loc: Loc,
        branch_patterns: I,
        target_type: &Type,
    ) -> Result<(), Error> {
        // Eventually we want to do this properly, perhaps following the
        // Lower Your Guards approach (https://dl.acm.org/doi/pdf/10.1145/3408989).
        //
        // For now we just check that the top-most patterns are exhaustive.

        match target_type {
            Type::Int => {
                // we don't yet handle exhaustiveness checking for int patterns
                Ok(())
            }
            Type::Bool => {
                let mut true_covered = false;
                let mut false_covered = false;
                for p in branch_patterns {
                    match p {
                        Pattern::Wildcard { .. } | Pattern::Var { .. } => return Ok(()),
                        Pattern::Constructor { name, .. } if name == "True" => {
                            true_covered = true;
                        }
                        Pattern::Constructor { name, .. } if name == "False" => {
                            false_covered = true;
                        }
                        _ => {}
                    }
                }
                if !true_covered {
                    return Err(Error::MissingCasePattern {
                        loc,
                        constructor: "True".to_string(),
                    });
                }
                if !false_covered {
                    return Err(Error::MissingCasePattern {
                        loc,
                        constructor: "False".to_string(),
                    });
                }
                Ok(())
            }
            Type::Tuple(_) => Ok(()),
            _ => {
                let type_name = {
                    let n;
                    let mut t = target_type;
                    loop {
                        match t {
                            Type::Named(name) => {
                                n = name;
                                break;
                            }
                            Type::App { head, .. } => {
                                t = head;
                            }
                            Type::Var(_) => {
                                // If the type is a variable, we can't know what patterns are
                                // valid.
                                // If we're reached this case it's because we haven't yet solved
                                // the required constraints to know what the actual type is.
                                return Ok(());
                            }
                            Type::Func(_, _) => {
                                // We can't pattern match functions, so don't bother with
                                // exhaustiveness checking.
                                return Ok(());
                            }
                            _ => unreachable!("{:?}", t),
                        }
                    }
                    n
                };
                // We don't handle lists yet
                if *type_name == GlobalName::builtin("List") {
                    return Ok(());
                }
                let mut all_constructors: HashSet<&str> = self
                    .constructors
                    .iter()
                    .filter(|(_, (t, _, _))| t == type_name)
                    .map(|(n, _)| n.name())
                    .collect();

                for p in branch_patterns {
                    match p {
                        Pattern::Var { .. } | Pattern::Wildcard { .. } | Pattern::Tuple { .. } => {
                            return Ok(());
                        }
                        Pattern::Constructor { name, .. } => {
                            all_constructors.remove(name.as_str());
                        }
                        Pattern::ListNil { .. } => {
                            all_constructors.remove("Nil");
                        }
                        Pattern::ListCons { .. } => {
                            all_constructors.remove("Cons");
                        }
                        Pattern::Int { .. } => unreachable!(),
                    }
                }

                if all_constructors.is_empty() {
                    return Ok(());
                }
                Err(Error::MissingCasePattern {
                    loc,
                    constructor: all_constructors.into_iter().next().unwrap().to_string(),
                })
            }
        }
    }

    fn infer_var(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        path: &Path,
        var: &Var,
        loc: Loc,
    ) -> Result<Type, Error> {
        match var {
            Var::Local(s) => self.lookup_local(local_variables, type_variables, path, s, loc),
            Var::Global(ns, s) => {
                let name = self.imports.lookup(loc, path, ns, s)?;
                self.lookup_global(type_variables, &name, loc)
            }
            Var::Constructor(ns, s) => {
                let ctor_name = match s.as_str() {
                    "True" | "False" => GlobalName::builtin(s),
                    _ => self.imports.lookup(loc, path, ns, s)?,
                };
                self.lookup_constructor(type_variables, &ctor_name, loc)
            }
            Var::Operator(op) => match op {
                Operator::Add | Operator::Sub | Operator::Mul => Ok(Type::Func(
                    Box::new(Type::Int),
                    Box::new(Type::Func(Box::new(Type::Int), Box::new(Type::Int))),
                )),
                Operator::Lt => Ok(Type::Func(
                    Box::new(Type::Int),
                    Box::new(Type::Func(Box::new(Type::Int), Box::new(Type::Bool))),
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
        path: &Path,
        target_type: &Type,
        branch: &CaseBranch,
    ) -> Result<Type, Error> {
        match &branch.pattern {
            Pattern::Int { loc, .. } => {
                // The target type must be Int
                self.assert_type_eq(type_variables, &target_type, &Type::Int, *loc)?;
                self.infer_expr(local_variables, type_variables, path, &branch.rhs)
            }
            Pattern::Wildcard { .. } => {
                self.infer_expr(local_variables, type_variables, path, &branch.rhs)
            }
            Pattern::Var { .. } => todo!(),
            Pattern::ListNil { loc, .. } => {
                // The target type must be List a for some a
                let var = self.make_fresh_var(type_variables);
                let list_type = self.make_list_type(var);
                self.assert_type_eq(type_variables, &target_type, &list_type, *loc)?;
                self.infer_expr(local_variables, type_variables, path, &branch.rhs)
            }
            Pattern::ListCons { .. } => {
                todo!()
            }
            Pattern::Constructor {
                name, args, loc, ..
            } => {
                // Lookup the type of the constructor and check it matches the target type.
                // Assume the type is defined in this file
                let ctor_name = GlobalName::named(path, name);
                let ctor_ty = self.lookup_constructor(type_variables, &ctor_name, *loc)?;
                self.assert_type_eq(type_variables, &target_type, &ctor_ty, *loc)?;

                // Check the constructor has the right number of args
                let ctor_ty_args = ctor_ty.func_args();
                let num_args_in_ctor_type = ctor_ty_args.len() - 1; // last elem is the result type
                if num_args_in_ctor_type != args.len() {
                    return Err(Error::CaseBranchArgNumberMismatch {
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
                        _ => todo!(),
                    }
                }
                let local_variables = local_variables.extend(new_vars);

                // Infer the rhs
                self.infer_expr(&local_variables, type_variables, path, &branch.rhs)
            }
            Pattern::Tuple { elems, loc } => {
                // The target type must be a tuple type with the same number of elements
                let mut vars = vec![];
                let mut new_locals = HashMap::new();
                for pattern in elems {
                    let var = self.make_fresh_var(type_variables);
                    // Check each subpattern, and collect any bound variables
                    new_locals.extend(self.check_match_branch_pattern(
                        type_variables,
                        path,
                        pattern,
                        &var,
                    )?);
                    vars.push(var);
                }
                let tuple_type = Type::Tuple(vars.clone());
                self.assert_type_eq(type_variables, &target_type, &tuple_type, *loc)?;

                // Infer the rhs
                let local_variables = local_variables.extend(new_locals);
                self.infer_expr(&local_variables, type_variables, path, &branch.rhs)
            }
        }
    }

    fn lookup_global(
        &self,
        type_variables: &mut TypeVariables,
        name: &GlobalName,
        loc: Loc,
    ) -> Result<Type, Error> {
        match self.functions.get(&name) {
            Some((_, ty)) => {
                // This function type may have type variables that we must instantiate.
                let (ty, vars) = self.generate_fresh_type_variables(ty.clone(), type_variables);
                for var in vars {
                    type_variables.insert(var, VarState::Unsolved);
                }
                Ok(ty.clone())
            }
            None => Err(Error::UnknownVariable(loc, name.to_string())),
        }
    }

    fn lookup_local(
        &self,
        local_variables: &LocalVariables<Type>,
        type_variables: &mut TypeVariables,
        path: &Path,
        name: &str,
        loc: Loc,
    ) -> Result<Type, Error> {
        // First look in the local variables
        match local_variables.lookup(name) {
            Some(ty) => Ok(ty.clone()),
            None => {
                // Then look at top-level bindings in the current file
                match self.lookup_global(type_variables, &GlobalName::named(path, name), loc) {
                    Ok(ty) => Ok(ty.clone()),
                    Err(_) => Err(Error::UnknownVariable(loc, name.to_string())),
                }
            }
        }
    }

    fn lookup_constructor(
        &self,
        type_variables: &mut TypeVariables,
        name: &GlobalName,
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

        match (expected, actual) {
            (Type::Var(expected_var), Type::Var(actual_var)) => {
                self.assert_var_eq(type_variables, expected_var, actual_var, loc)
            }
            (Type::Var(expected_var), actual) => {
                self.try_solve_type_var(type_variables, expected_var, actual, loc, false)?;
                Ok(())
            }
            (expected, Type::Var(actual_var)) => {
                self.try_solve_type_var(type_variables, actual_var, expected, loc, true)?;
                Ok(())
            }
            (Type::Tuple(elems_expected), Type::Tuple(elems_actual)) => {
                if elems_expected.len() != elems_actual.len() {
                    return Err(Error::TupleUnexpectedNumberOfElements {
                        loc,
                        expected_number: elems_expected.len(),
                        actual_number: elems_actual.len(),
                    });
                }
                for (exp, act) in elems_expected.iter().zip(elems_actual.iter()) {
                    self.assert_type_eq(type_variables, exp, act, loc)?;
                }
                Ok(())
            }
            (Type::Int, _)
            | (_, Type::Int)
            | (Type::Bool, _)
            | (_, Type::Bool)
            | (Type::Char, _)
            | (_, Type::Char)
            | (Type::Str, _)
            | (_, Type::Str)
            | (_, Type::Tuple(_))
            | (Type::Tuple(_), _) => Err(Error::ExpectedType {
                loc,
                expected: expected.clone(),
                actual: actual.clone(),
            }),
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
                // If the application heads match, try to equate their arguments
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
                unreachable!("unknown type variable {expected}");
            }
            Some(t) => {
                match t {
                    VarState::Unsolved => {
                        debug!("solved {expected}");
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
                            // If actual is also a type variable, try solving them the other way
                            // around.
                            if let Type::Var(actual) = actual {
                                self.try_solve_type_var(
                                    type_variables,
                                    actual,
                                    &Type::Var(expected.to_string()),
                                    loc,
                                    true,
                                )
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
    }

    /// Check the well-formedness of all registered types.
    /// We do this after registering, so that circular references are allowed.
    /// If we check each type up-front, we have to register them in reverse dependency order.
    pub fn check_all_types(&self) -> Result<(), Error> {
        for (type_name, loc, ctor_type) in self.constructors.values() {
            match type_name {
                GlobalName::Builtin(_) => {
                    // No need to check builtin types.
                }
                GlobalName::Named(path, _) => match self.types.get(type_name) {
                    Some(type_params) => {
                        self.check_type(path, ctor_type, *loc, type_params)?;
                    }
                    None => {
                        return Err(Error::UnknownType(*loc, type_name.clone()));
                    }
                },
            }
        }
        Ok(())
    }

    pub fn check_type(
        &self,
        path: &Path,
        ty: &Type,
        loc: Loc,
        vars_in_scope: &[String],
    ) -> Result<(), Error> {
        // Check that all mentioned types exist.
        match ty {
            Type::Named(name) => {
                if !self.types.contains_key(&name) {
                    return Err(Error::UnknownType(loc, name.clone()));
                }
            }
            Type::Func(f, x) => {
                self.check_type(path, f, loc, vars_in_scope)?;
                self.check_type(path, x, loc, vars_in_scope)?;
            }
            Type::Int | Type::Bool | Type::Str | Type::Char => {}
            Type::Tuple(elems) => {
                for e in elems {
                    self.check_type(path, e, loc, vars_in_scope)?;
                }
            }
            Type::App { head, args } => {
                self.check_type(path, head, loc, vars_in_scope)?;
                for arg in args {
                    self.check_type(path, arg, loc, vars_in_scope)?;
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

    fn make_fresh_var(&self, type_variables: &mut TypeVariables) -> Type {
        let var = match self.rename("a", type_variables) {
            Some(var) => var,
            None => "a".to_string(),
        };
        type_variables.insert(var.clone(), VarState::Unsolved);
        Type::Var(var)
    }

    fn make_list_type(&self, elem_type: Type) -> Type {
        Type::App {
            head: Box::new(Type::Named(GlobalName::builtin("List"))),
            args: vec![elem_type],
        }
    }

    fn make_fresh_list_type(&self, type_variables: &mut TypeVariables) -> Type {
        self.make_list_type(self.make_fresh_var(type_variables))
    }

    fn type_from_source_type(&self, path: &Path, source_type: &SourceType) -> Result<Type, Error> {
        match source_type {
            SourceType::Named(_, None, n) if n == "List" => {
                Ok(Type::Named(GlobalName::builtin("List")))
            }
            SourceType::Named(loc, ns, n) => {
                self.imports.lookup(*loc, path, ns, n).map(Type::Named)
            }
            SourceType::Func(_, f, x) => {
                let f = self.type_from_source_type(path, f)?;
                let x = self.type_from_source_type(path, x)?;
                Ok(Type::Func(Box::new(f), Box::new(x)))
            }
            SourceType::Int(_) => Ok(Type::Int),
            SourceType::Bool(_) => Ok(Type::Bool),
            SourceType::Str(_) => Ok(Type::Str),
            SourceType::Char(_) => Ok(Type::Char),
            SourceType::App { head, args, .. } => {
                let head = self.type_from_source_type(path, head)?;
                let args = args
                    .iter()
                    .map(|arg| self.type_from_source_type(path, arg))
                    .collect::<Result<_, _>>()?;
                Ok(Type::App {
                    head: Box::new(head),
                    args,
                })
            }
            SourceType::Var(_, v) => Ok(Type::Var(v.to_string())),
            SourceType::Tuple { elems, .. } => Ok(Type::Tuple(
                elems
                    .into_iter()
                    .map(|e| self.type_from_source_type(path, e))
                    .collect::<Result<_, _>>()?,
            )),
        }
    }
    fn make_constructor_type(
        &self,
        loc: Loc,
        path: &Path,
        namespace: Option<Namespace>,
        type_name: &str,
        params: &Vec<String>,
        constructor: &TypeConstructor,
    ) -> Result<Type, Error> {
        // Create a function type with the constructor's type as the result
        // e.g.
        // type Foo { MkFoo Int Bool Char }
        // has type
        // MkFoo : Int -> Bool -> Char -> Foo

        let mut ty = Type::Named(self.imports.lookup(loc, path, &namespace, type_name)?);

        if !params.is_empty() {
            let args = params.iter().map(|p| Type::Var(p.to_string())).collect();
            ty = Type::App {
                head: Box::new(ty),
                args,
            };
        }

        for a in constructor.arguments.iter().rev().cloned() {
            ty = Type::Func(
                Box::new(self.type_from_source_type(path, &a)?),
                Box::new(ty),
            );
        }
        Ok(ty)
    }
}

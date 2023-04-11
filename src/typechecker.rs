use std::collections::{HashMap, HashSet, VecDeque};

use crate::ast::*;

const TYPE_INT: Type = Type::Int;

#[derive(Debug)]
pub enum Error {
    TypeAlreadyDefined(String),
    UnknownType(String),
    UnknownVariable(String),
    UnknownConstructor(String),
    EmptyMatch,
    ExpectedType{ expected: Type, actual: Type },
    MatchBranchArgNumberMismatch { number_of_args_in_branch: usize, number_of_args_in_constructor_type: usize },
    CannotInferTypeOfFunctions,
    ExpectedFunctionType { actual_type: Type },
}

pub struct Typechecker {
    constructors: HashMap<String, Type>,
    types: HashSet<String>,
    functions: HashMap<String, Type>,

}

impl Typechecker {
    pub fn new() -> Self {
        Self {
            constructors: HashMap::new(),
            types: HashSet::new(),
            functions: HashMap::new()
        }
    }

    pub fn register_type(&mut self, name: &str, constructors: &[TypeConstructor]) -> Result<(), Error> {
        // Check that type name is not already in use
        if self.types.contains(name) {
            return Err(Error::TypeAlreadyDefined(name.to_string()))
        }

        // Check that constructors are well-formed
        self.types.insert(name.to_string());
        for ctor in constructors {
            let ctor_type = make_constructor_type(&name, &ctor);
            // Note: we don't check the type now.
            // That happens later, see `check_all_types`.
            self.constructors.insert(ctor.name.to_string(), ctor_type);
        }
        Ok(())
    }

    pub fn register_func(&mut self, name: &str, r#type: &Type) -> Result<(), Error> {
        // Check that function name is not already in use
        // Check that type is well-formed
        self.functions.insert(name.to_string(), r#type.clone());
        Ok(())
    }

    pub fn check_func(&self, func: &Expr, expected_type: &Type) -> Result<(), Error> {
        self.check_expr(&LocalVariables::new(), func, expected_type)
    }

    fn check_expr(&self, local_variables: &LocalVariables, expr: &Expr, expected_type: &Type) -> Result<(), Error> {
        match expr {
            Expr::Int(_) => self.assert_type_eq(expected_type, &TYPE_INT),
            Expr::Var(v) => {
                let ty = self.infer_var(local_variables, v)?;
                self.assert_type_eq(expected_type, &ty)
            }
            Expr::Match { target, branches } => {
                // Infer the type of the target
                let target_type = self.infer_var(local_variables, target)?;

                // There must be at least one branch
                if branches.is_empty() {
                    return Err(Error::EmptyMatch)
                }

                self.check_match_expr(local_variables, branches, &target_type, &expected_type)?;

                Ok(())
            }
            Expr::Func { args, body } => {
                // Deconstruct expected type
                let mut func_arg_types = expected_type.func_args().into_iter();

                let mut new_locals = HashMap::new();

                // Add each arg to local variables
                for arg in args {
                    match func_arg_types.next() {
                        Some(arg_type) => {
                            self.check_pattern(arg, arg_type)?;
                            let Pattern::Var(v) = arg;
                            new_locals.insert(v.to_string(), arg_type.clone());
                        }
                        None => { todo!("what error?"); }
                    }
                }

                // Reconstruct remaining args into result type
                let result_type = Type::from_func_args(&func_arg_types.collect());

                // TODO: use new locals when checking body

                self.check_expr(&LocalVariables::extend(&local_variables, new_locals), body, &result_type)
            }
            Expr::App { head, args } => {
                // Infer type of head
                let head_type = self.infer_expr(local_variables, head)?;

                // Deconstruct type
                let mut head_type_args = head_type.func_args().into_iter();

                for arg in args {
                    match head_type_args.next() {
                        Some(ty) => {
                            self.check_expr(local_variables, arg, ty)?;
                        },
                        None => {
                            return todo!("what error to return here?");
                        }
                    }
                }

                // Reconstruct result type
                let result_type = Type::from_func_args(&head_type_args.collect());
                self.assert_type_eq(expected_type, &result_type)?;
                Ok(())
            }
        }
    }

    fn infer_expr(&self, local_variables: &LocalVariables, expr: &Expr) -> Result<Type, Error> {
        match expr {
            Expr::Int(_) => Ok(TYPE_INT),
            Expr::Var(v) => self.infer_var(local_variables, v),
            Expr::Match { target, branches } => {
                // Infer the type of the target
                let target_type = self.infer_var(local_variables, target)?;

                // There must be at least one branch
                if branches.is_empty() {
                    return Err(Error::EmptyMatch)
                }

                // Infer the return type of the first branch
                let result_type = self.infer_match_branch(local_variables, &target_type, &branches[0])?;

                self.check_match_expr(local_variables, branches, &target_type, &result_type)?;

                Ok(result_type)
            }
            Expr::Func { .. } => {
                Err(Error::CannotInferTypeOfFunctions)
            }
            Expr::App { head, args } => {
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
                                Some(arg_type) => { self.check_expr(local_variables, arg, arg_type)?; }
                                None => { return todo!("what error to return here?"); }
                            }
                        }

                        // Construct the result type from the remaining func_args
                        Ok(Type::from_func_args(&func_arg_types.collect()))
                    }
                    _ => {
                        return Err(Error::ExpectedFunctionType { actual_type: head_ty.clone() });
                    }
                }
            }
        }
    }

    fn check_pattern(&self, pattern: &Pattern, expected_type: &Type) -> Result<(), Error> {
        Ok(())
    }

    fn check_match_expr(&self, local_variables: &LocalVariables, branches: &Vec<MatchBranch>, target_type: &Type, result_type: &Type) -> Result<(), Error> {
        // There must be at least one branch
        if branches.is_empty() {
            return Err(Error::EmptyMatch)
        }

        // For each subsequent branch...
        for branch in branches[1..].iter() {
            // Check the constructor yields `target_type`
            let ctor_ty = match self.constructors.get(&branch.constructor) {
                None => { return Err(Error::UnknownConstructor(branch.constructor.clone())); }
                Some(ty) => {
                    self.assert_type_eq(&target_type, &ty)?;
                    ty
                }
            };

            // Check the constructor has the right number of args
            let ctor_ty_args = ctor_ty.func_args();
            let num_args_in_ctor_type = ctor_ty_args.len();
            if num_args_in_ctor_type != branch.args.len() {
                return Err(Error::MatchBranchArgNumberMismatch {
                    number_of_args_in_branch: branch.args.len(),
                    number_of_args_in_constructor_type: num_args_in_ctor_type
                });
            }

            // Add each pattern to the set of local variables
            let mut new_vars = HashMap::new();
            for (pattern, ty) in branch.args.iter().zip(ctor_ty_args.into_iter()) {
                let Pattern::Var(n) = pattern;
                new_vars.insert(n.to_string(), ty.clone());
            }
            let local_variables = LocalVariables::extend(&local_variables, new_vars);

            // Check the branch rhs has result_type
            self.check_expr(&local_variables, &branch.rhs, result_type)?;
        }

        Ok(())
    }

    fn infer_var(&self, local_variables: &LocalVariables, var: &Var) -> Result<Type, Error> {
        match var {
            Var::Local(s) => {
                self.lookup(local_variables, s)
            }
            Var::Constructor(s) => {
                match self.constructors.get(s) {
                    Some(ty) => Ok(ty.clone()),
                    None => Err(Error::UnknownConstructor(s.to_string()))
                }
            }
            Var::Operator(op) => {
                match op {
                    Operator::Add | Operator::Sub | Operator::Mul => Ok(Type::Func(Box::new(Type::Int), Box::new(Type::Func(Box::new(Type::Int), Box::new(Type::Int)))))
                }
            }
        }
    }

    fn infer_match_branch(&self, local_variables: &LocalVariables, target_ty: &Type, branch: &MatchBranch) -> Result<Type, Error> {
        todo!()
    }

    fn lookup(&self, local_variables: &LocalVariables, name: &str) -> Result<Type, Error> {
        match local_variables.lookup(name) {
            Some(ty) => Ok(ty.clone()),
            None => {
                match self.functions.get(name) {
                    Some(ty) => Ok(ty.clone()),
                    None => Err(Error::UnknownVariable(name.to_string()))
                }
            }
        }
    }

    fn assert_type_eq(&self, expected: &Type, actual: &Type) -> Result<(), Error> {
        if expected == actual {
            return Ok(());
        }
        Err(Error::ExpectedType { expected: expected.clone(), actual: actual.clone() })
    }

    /// Check the well-formedness of all registered types.
    /// We do this after registering, so that circular references are allowed.
    /// If we check each type up-front, we have to register them in reverse dependency order.
    pub fn check_all_types(&self) -> Result<(), Error> {
        for ctor_type in self.constructors.values() {
            self.check_type(ctor_type)?;
        }
        Ok(())
    }

    pub fn check_type(&self, ty: &Type) -> Result<(), Error> {
        // Check that all mentioned types exist.
        match ty {
            Type::Named(n) => {
                if !self.types.contains(n) {
                    return Err(Error::UnknownType(n.to_string()))
                }
            },
            Type::Func(f, x) => {
                self.check_type(f)?;
                self.check_type(x)?;
            },
            Type::Int => {}
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
        ty = Type::Func(Box::new(a), Box::new(ty));
    }
    ty
}

enum LocalVariables<'a> {
    One(HashMap<String, Type>),
    More(HashMap<String, Type>, &'a LocalVariables<'a>)
}

impl<'a> LocalVariables<'a> {
    pub fn new() -> Self {
        Self::One(HashMap::new())
    }

    pub fn lookup(&self, name: &str) -> Option<&Type> {
        match self {
            Self::One(stack) => match stack.get(name) {
                Some(ty) => Some(ty),
                None => None
            }
            Self::More(stack, rest) => match stack.get(name) {
                Some(ty) => Some(ty),
                None => rest.lookup(name),
            }
        }
    }

    pub fn extend(vars: &'a Self, stack: HashMap<String, Type>) -> LocalVariables<'a> {
        Self::More(stack, &vars)
    }
}

use std::collections::HashMap;

use tracing::debug;

use crate::ast::{Expr, LetBinding, Operator, Pattern, TypeConstructor, Var};
use crate::local_variables::LocalVariables;

pub struct Interpreter {
    functions: HashMap<String, Expr>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
        }
    }

    pub fn register_type(&mut self, _name: &str, _constructors: &[TypeConstructor]) {
        // do we actually need to store this info?
    }

    pub fn register_func(&mut self, name: &str, body: &Expr) {
        self.functions.insert(name.to_string(), (*body).clone());
    }

    pub fn eval(&self, locals: &LocalVariables<Value>, expr: &Expr) -> Result<Value, Error> {
        debug!(locals = ?locals.names(), "eval");
        match expr {
            Expr::Int(_, n) => Ok(Value::Int(*n)),
            Expr::List(_, elems) => {
                debug!("eval_list");
                // Evaluate each element
                let mut elem_values = vec![];
                for elem in elems {
                    elem_values.push(self.eval(locals, elem)?);
                }
                // Construct a linked list. We must work backwards to build up from the last
                // element.
                elem_values.reverse();
                let mut value = Value::ListNil;
                for v in elem_values {
                    value = Value::ListCons(Box::new(v), Box::new(value));
                }
                Ok(value)
            }
            Expr::App { head, args, .. } => {
                debug!(?head, ?args, locals = ?locals.names(), "eval_app");
                let head_value = self.eval(locals, head)?;
                self.eval_app(locals, head_value, args)
            }
            Expr::Func { args, body, .. } => {
                debug!(?args, ?body, "eval_func");
                // If the function is nullary, evaluate its body directly.
                if args.is_empty() {
                    self.eval(locals, body)
                } else {
                    // Store any captured variables by looking for free variable references in the
                    // function.
                    let mut captured_locals = HashMap::new();
                    for v in expr.free_variables() {
                        if let Some(val) = self.lookup_local_var(locals, v)? {
                            captured_locals.insert(v.clone(), val);
                        }
                    }
                    Ok(Value::Func {
                        locals: captured_locals,
                        params: args.iter().map(|(_, name)| name).cloned().collect(),
                        applied_args: vec![],
                        // TODO: avoid cloning body
                        body: (**body).clone(),
                    })
                }
            }
            Expr::Case {
                target, branches, ..
            } => {
                // Evaluate the target
                let target_value = self.eval(locals, target)?;

                debug!(?target_value, ?branches, "eval_case");

                // Check its constructor.
                match target_value {
                    Value::Int(n) => {
                        // Find a branch that matches n
                        for branch in branches {
                            match branch.pattern {
                                Pattern::Int { value, .. } if value == n => {
                                    return self.eval(locals, &branch.rhs);
                                }
                                Pattern::Wildcard { .. } => {
                                    return self.eval(locals, &branch.rhs);
                                }
                                _ => {}
                            }
                        }
                        Err(Error::NoMatchingBranch)
                    }
                    Value::Bool(b) => {
                        // Find a branch that matches b
                        for branch in branches {
                            match &branch.pattern {
                                Pattern::Constructor { name, .. }
                                    if (b && name == "True") || (!b && name == "False") =>
                                {
                                    return self.eval(locals, &branch.rhs);
                                }
                                Pattern::Wildcard { .. } => {
                                    return self.eval(locals, &branch.rhs);
                                }
                                _ => {}
                            }
                        }
                        Err(Error::NoMatchingBranch)
                    }
                    Value::Constructor { name, applied_args } => {
                        // Find a branch that matches the constructor name
                        for branch in branches {
                            debug!(?branch, "checking branch");
                            match &branch.pattern {
                                Pattern::Constructor { name: n, args, .. } if *n == name => {
                                    match self.match_patterns(args.as_slice(), &applied_args) {
                                        Some(new_locals) => {
                                            debug!(
                                                ?branch,
                                                ?name,
                                                ?applied_args,
                                                "case match pass"
                                            );
                                            let mut owned_new_locals = HashMap::new();
                                            // TODO: it should be possible to avoid this clone.
                                            for (k, v) in new_locals.into_iter() {
                                                owned_new_locals.insert(k, v.clone());
                                            }
                                            return self.eval(
                                                &locals.extend(owned_new_locals),
                                                &branch.rhs,
                                            );
                                        }
                                        None => {
                                            debug!(
                                                ?branch,
                                                ?name,
                                                ?applied_args,
                                                "case match failure"
                                            );
                                        }
                                    }
                                }
                                Pattern::Wildcard { .. } => {
                                    return self.eval(locals, &branch.rhs);
                                }
                                _ => {}
                            }
                        }
                        debug!(?branches, ?name, "case match no match");
                        Err(Error::NoMatchingBranch)
                    }
                    Value::ListNil => {
                        debug!("checking case for ListNil");
                        for branch in branches {
                            debug!(?branch, "checking branch");
                            match &branch.pattern {
                                Pattern::Constructor { name, args, .. } if name == "Nil" => {
                                    assert_eq!(args.len(), 0);
                                    return self.eval(locals, &branch.rhs);
                                }
                                Pattern::Wildcard { .. } => {
                                    return self.eval(locals, &branch.rhs);
                                }
                                _ => {}
                            }
                        }
                        Err(Error::NoMatchingBranch)
                    }
                    Value::ListCons(head, tail) => {
                        debug!(?head, ?tail, "finding branch for Cons");
                        let applied_args = [*head, *tail];
                        // Find a branch that matches the constructor name
                        for branch in branches {
                            debug!(?branch, "checking branch");
                            match &branch.pattern {
                                Pattern::Constructor { name: n, args, .. } if n == "Cons" => {
                                    match self.match_patterns(args.as_slice(), &applied_args) {
                                        Some(new_locals) => {
                                            let mut owned_new_locals = HashMap::new();
                                            // TODO: it should be possible to avoid this clone.
                                            for (k, v) in new_locals.into_iter() {
                                                owned_new_locals.insert(k, v.clone());
                                            }
                                            return self.eval(
                                                &locals.extend(owned_new_locals),
                                                &branch.rhs,
                                            );
                                        }
                                        None => {}
                                    }
                                }
                                Pattern::Wildcard { .. } => {
                                    return self.eval(locals, &branch.rhs);
                                }
                                _ => {}
                            }
                        }
                        Err(Error::NoMatchingBranch)
                    }
                    _ => Err(Error::InvalidMatchTarget),
                }
            }
            Expr::Var(_, v) => {
                debug!("eval_var");
                self.eval_var(locals, v)
            }
            Expr::Let { bindings, body, .. } => {
                debug!(?bindings, ?body, "eval_let");
                let mut new_locals = HashMap::new();
                for LetBinding { name, value, .. } in bindings {
                    let val = self.eval(&locals.extend(new_locals.clone()), &value)?;
                    new_locals.insert(name.to_string(), val);
                }
                let locals = locals.extend(new_locals);
                return self.eval(&locals, &body);
            }
        }
    }

    fn eval_app(
        &self,
        locals: &LocalVariables<Value>,
        head: Value,
        args: &[Expr],
    ) -> Result<Value, Error> {
        match head {
            Value::Int(_) | Value::Bool(_) | Value::ListNil | Value::ListCons(_, _) => {
                return Err(Error::ApplicationOfNonFunction)
            }
            Value::Func {
                params,
                locals: captured_locals,
                mut applied_args,
                body,
            } => {
                assert!(params.len() > applied_args.len());

                // Evaluate and push args onto the function,
                // stopping if we've saturated it.
                let mut i = 0;
                while applied_args.len() < params.len() {
                    match args.get(i) {
                        Some(arg) => {
                            applied_args.push(self.eval(locals, arg)?);
                        }
                        None => {
                            break;
                        }
                    }
                    i += 1;
                }

                if applied_args.len() == params.len() {
                    // If we've saturated the function, evaluate its body.
                    let result = {
                        // TODO: should we allow access to locals here?
                        // shouldn't the function only see locals captured when it was defined?
                        let locals =
                            locals.extend(self.build_locals_from_func_args(params, applied_args));
                        let locals = locals.extend(captured_locals);
                        self.eval(&locals, &body)?
                    };

                    // If we have any args remaining, apply the result to them.
                    if i < args.len() {
                        self.eval_app(locals, result, &args[i..])
                    } else {
                        Ok(result)
                    }
                } else {
                    // otherwise, return it
                    Ok(Value::Func {
                        locals: captured_locals,
                        params,
                        applied_args,
                        body,
                    })
                }
            }
            Value::Operator {
                op,
                mut applied_args,
            } => {
                let num_params = num_params_for_op(op);
                assert!(num_params > applied_args.len());

                // Operators don't return functions and can't be partially applied,
                // so we can assume that we have exactly the right number of args.

                for arg in args {
                    applied_args.push(self.eval(locals, arg)?);
                }

                Ok(eval_operator(op, applied_args))
            }
            Value::Constructor {
                name,
                mut applied_args,
            } => {
                // Special case: if the constructor is Cons and we have 2 args, create a ListCons
                if name == "Cons" && applied_args.len() + args.len() == 2 {
                    if applied_args.is_empty() {
                        let arg1 = self.eval(locals, &args[0])?;
                        let arg2 = self.eval(locals, &args[1])?;
                        Ok(Value::ListCons(Box::new(arg1), Box::new(arg2)))
                    } else {
                        // Assuming all App nodes have at least 1 arg,
                        // we must have 1 arg each in applied_args and args.
                        assert_eq!(applied_args.len(), 1);
                        assert_eq!(args.len(), 1);
                        let arg1 = applied_args.pop().unwrap();
                        let arg2 = self.eval(locals, &args[1])?;
                        Ok(Value::ListCons(Box::new(arg1), Box::new(arg2)))
                    }
                } else {
                    for arg in args {
                        applied_args.push(self.eval(locals, arg)?);
                    }

                    Ok(Value::Constructor { name, applied_args })
                }
            }
        }
    }

    fn eval_var(&self, locals: &LocalVariables<Value>, var: &Var) -> Result<Value, Error> {
        debug!(?var, "eval_var");
        match var {
            Var::Local(v) => match locals.lookup(v) {
                Some(val) => Ok(val.clone()),
                None => match self.functions.get(v) {
                    Some(func) => self.eval(locals, func),
                    None => Err(Error::UndefinedVariable(v.to_string())),
                },
            },
            Var::Constructor(name) => Ok(Value::Constructor {
                name: name.to_string(),
                applied_args: vec![],
            }),
            Var::Operator(op) => Ok(Value::Operator {
                op: *op,
                applied_args: vec![],
            }),
        }
    }

    /// If the variable refers to a global function, returns None.
    fn lookup_local_var(
        &self,
        locals: &LocalVariables<Value>,
        var: &str,
    ) -> Result<Option<Value>, Error> {
        match locals.lookup(var) {
            Some(val) => Ok(Some(val.clone())),
            None => match self.functions.get(var) {
                Some(_) => Ok(None),
                None => Err(Error::UndefinedVariable(var.to_string())),
            },
        }
    }

    fn build_locals_from_func_args(
        &self,
        params: Vec<String>,
        args: Vec<Value>,
    ) -> HashMap<String, Value> {
        let mut new_locals = HashMap::new();
        for (param, arg) in params.into_iter().zip(args.into_iter()) {
            new_locals.insert(param.to_string(), arg);
        }
        new_locals
    }

    /// Match each pattern to each arg.
    /// If all args match their patterns, return a HashMap of the bound locals.
    fn match_patterns<'a, 'b>(
        &'a self,
        patterns: &[Pattern],
        args: &'b [Value],
    ) -> Option<HashMap<String, &'b Value>> {
        assert_eq!(patterns.len(), args.len());
        let mut new_locals = HashMap::new();
        for (pattern, arg) in patterns.into_iter().zip(args.into_iter()) {
            match (pattern, &arg) {
                (Pattern::Var { name, .. }, _) => {
                    new_locals.insert(name.clone(), arg);
                }
                (
                    Pattern::Constructor {
                        name, args: c_args, ..
                    },
                    Value::ListNil,
                ) if name == "Nil" => {
                    assert_eq!(c_args.len(), 0);
                }
                (
                    Pattern::Constructor {
                        name,
                        args: _c_args,
                        ..
                    },
                    Value::ListCons(_head, _tail),
                ) if name == "Cons" => {
                    todo!("bind constructor args");
                }
                (
                    Pattern::Constructor {
                        name, args: c_args, ..
                    },
                    Value::Constructor { name: n, .. },
                ) if n == name => {
                    if !c_args.is_empty() {
                        todo!("bind constructor args");
                    }
                }
                (Pattern::Constructor { .. }, _) => {
                    return None;
                }
                (Pattern::Int { value, .. }, Value::Int(n)) if value == n => {}
                (Pattern::Int { .. }, _) => {
                    return None;
                }
                (Pattern::Wildcard { .. }, _) => {}
            }
        }
        Some(new_locals)
    }
}

fn num_params_for_op(op: Operator) -> usize {
    match op {
        Operator::Add => 2,
        Operator::Sub => 2,
        Operator::Mul => 2,
        Operator::Eq => 2,
    }
}

fn eval_operator(op: Operator, args: Vec<Value>) -> Value {
    assert_eq!(args.len(), 2);

    match op {
        Operator::Add | Operator::Sub | Operator::Mul => {
            let arg1 = match args[0] {
                Value::Int(n) => n,
                _ => unreachable!(),
            };
            let arg2 = match args[1] {
                Value::Int(n) => n,
                _ => unreachable!(),
            };

            let result = match op {
                Operator::Add => arg1 + arg2,
                Operator::Sub => arg1 - arg2,
                Operator::Mul => arg1 * arg2,
                _ => unreachable!(),
            };

            Value::Int(result)
        }
        Operator::Eq => Value::Bool(args[0] == args[1]),
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Bool(bool),
    ListCons(Box<Value>, Box<Value>),
    ListNil,
    Func {
        // local variables read by the function
        // these are the variables that were in scope when it was defined and are mentioned in the
        // function body.
        locals: HashMap<String, Value>,
        params: Vec<String>,
        applied_args: Vec<Value>,
        body: Expr,
    },
    Operator {
        op: Operator,
        applied_args: Vec<Value>,
    },
    Constructor {
        name: String,
        applied_args: Vec<Value>,
    },
}

impl PartialEq for Value {
    /// Panics if you try to compare two values of different types, e.g. Bool and Int
    /// This is to surface typechecking bugs.
    /// Returns false if you try to compare functions.
    fn eq(&self, other: &Value) -> bool {
        match self {
            Self::Func { .. } => false,
            Self::Int(n) => match other {
                Self::Int(m) => n == m,
                _ => unreachable!(),
            },
            Self::Bool(n) => match other {
                Self::Bool(m) => n == m,
                _ => unreachable!(),
            },
            Self::Operator {
                op: op_l,
                applied_args: args_l,
            } => match other {
                Self::Operator {
                    op: op_r,
                    applied_args: args_r,
                } => op_l == op_r && args_l == args_r,
                _ => unreachable!(),
            },
            Self::Constructor {
                name: name_l,
                applied_args: args_l,
            } => match other {
                Self::Constructor {
                    name: name_r,
                    applied_args: args_r,
                } => name_l == name_r && args_l == args_r,
                Self::ListNil => name_l == "Nil",
                _ => unreachable!("{:?} == {:?}", self, other),
            },
            Self::ListNil => match other {
                Self::ListNil => true,
                Self::ListCons(_, _) => false,
                Self::Constructor { name, .. } => name == "Nil",
                _ => unreachable!(),
            },
            Self::ListCons(h1, t1) => match other {
                Self::ListNil => false,
                Self::ListCons(h2, t2) => h1 == h2 && t1 == t2,
                _ => unreachable!(),
            },
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Func { .. } => write!(f, "<func>"),
            Value::Operator { .. } => write!(f, "<func>"),
            Value::Constructor { name, applied_args } => {
                write!(f, "{}", name)?;
                for arg in applied_args {
                    write!(f, " {}", arg)?;
                }
                Ok(())
            }
            Value::ListCons(head, tail) => display_nonempty_list(f, &head, &tail),
            Value::ListNil => write!(f, "[]"),
        }
    }
}

fn display_nonempty_list<'a>(
    f: &mut std::fmt::Formatter<'_>,
    mut head: &'a Value,
    mut tail: &'a Value,
) -> Result<(), std::fmt::Error> {
    write!(f, "[")?;
    loop {
        write!(f, "{}", head)?;
        match &*tail {
            Value::ListNil => {
                break;
            }
            Value::ListCons(h, t) => {
                write!(f, ", ")?;
                head = &*h;
                tail = &*t;
            }
            _ => unreachable!(),
        }
    }
    write!(f, "]")
}

#[derive(Debug)]
pub enum Error {
    ApplicationOfNonFunction,
    UndefinedVariable(String),
    InvalidMatchTarget,
    NoMatchingBranch,
}

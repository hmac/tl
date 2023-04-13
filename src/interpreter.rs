use std::collections::HashMap;

use crate::ast::{Expr, TypeConstructor, Pattern, Var, Operator};
use crate::local_variables::LocalVariables;

pub struct Interpreter {
    functions: HashMap<String, Expr>
}

impl Interpreter {
    pub fn new() -> Self {
        Self { functions: HashMap::new() }
    }

    pub fn register_type(&mut self, _name: &str, _constructors: &[TypeConstructor]) {
        // do we actually need to store this info?
    }

    pub fn register_func(&mut self, name: &str, body: &Expr)  {
        self.functions.insert(name.to_string(), (*body).clone());
    }

    pub fn eval(&self, locals: &LocalVariables<Value>, expr: &Expr) -> Result<Value, Error> {
        match expr {
            Expr::Int(_, n) => Ok(Value::Int(*n)),
            Expr::App { head, args, .. } => {
                let head_value = self.eval(locals, head)?;
                match head_value {
                    Value::Int(_) => return Err(Error::ApplicationOfNonFunction),
                    Value::Func { params, mut applied_args, body } => {
                        assert!(params.len() > applied_args.len());

                        // Evaluate and push args onto the function,
                        // stopping if we've saturated it.
                        let mut i = 0;
                        while applied_args.len() < params.len() {
                            match args.get(i) {
                                Some(arg) => {
                                    applied_args.push(self.eval(locals, arg)?);
                                }
                                None => { break; }
                            }
                            i += 1;
                        }

                        // If we've saturated the function, evaluate its body.
                        if applied_args.len() == params.len() {
                            let new_locals = locals.extend(self.build_locals_from_func_args(params, applied_args));
                            self.eval(&new_locals, &body)
                        } else {
                            // Otherwise, return it
                            Ok(Value::Func { params, applied_args, body })
                        }
                    }
                    Value::Operator { op, mut applied_args } => {
                        let num_params = num_params_for_op(op);
                        assert!(num_params > applied_args.len());

                        // Operators don't return functions and can't be partially applied,
                        // so we can assume that we have exactly the right number of args.

                        for arg in args {
                            applied_args.push(self.eval(locals, arg)?);
                        }

                        Ok(eval_operator(op, applied_args))
                    }
                    Value::Constructor { name, mut applied_args } => {
                        for arg in args {
                            applied_args.push(self.eval(locals, arg)?);
                        }

                        Ok(Value::Constructor { name, applied_args })
                    }
                }
            }
            Expr::Func { args, body, .. } => {
                // If the function is nullary, evaluate its body directly.
                if args.is_empty() {
                    self.eval(locals, body)
                } else {
                    Ok(Value::Func {
                        params: args.clone(),
                        applied_args: vec![],
                        // TODO: avoid cloning body
                        body: (**body).clone(),
                    })
                }
            }
            Expr::Match { target, branches, .. } => {
                // Evaluate the target
                let target_value = self.eval_var(locals, target)?;

                // Check its constructor.
                match target_value {
                    Value::Int(_) => todo!(),
                    Value::Constructor { name, applied_args } => {
                        // Find a branch that matches the constructor name
                        match branches.iter().find(|branch| branch.constructor == name ) {
                            Some(branch) => {
                                // Bind the branch args
                                let new_locals = self.build_locals_from_func_args(branch.args.clone(), applied_args);
                                // Evaluate the rhs
                                self.eval(&locals.extend(new_locals), &branch.rhs)
                            }
                            None => {
                                Err(Error::NoMatchingBranch)
                            }
                        }
                    }
                    _ => Err(Error::InvalidMatchTarget)
                }
            }
            Expr::Var(_, v) => self.eval_var(locals, v)
        }
    }

    fn eval_var(&self, locals: &LocalVariables<Value>, var: &Var) -> Result<Value, Error> {
        match var {
            Var::Local(v) => {
                // Check locals first
                match locals.lookup(v) {
                    Some(val) => Ok(val.clone()),
                    None => {
                        match self.functions.get(v) {
                            Some(func) => {
                                self.eval(locals, func)
                            }
                            None => {
                                Err(Error::UndefinedVariable(v.to_string()))
                            }
                        }
                    }
                }
            },
            Var::Constructor(name) => Ok(Value::Constructor { name: name.to_string(), applied_args: vec![] }),
            Var::Operator(op) => {
                Ok(Value::Operator { op: *op, applied_args: vec![] })
            },
        }
    }

    fn build_locals_from_func_args(&self, params: Vec<Pattern>, args: Vec<Value>) -> HashMap<String, Value> {
        let mut new_locals = HashMap::new();
        for (param, arg) in params.into_iter().zip(args.into_iter()) {
            let Pattern::Var(_, p) = param;
            new_locals.insert(p.to_string(), arg);
        }
        new_locals
    }
}

fn num_params_for_op(op: Operator) -> usize {
    match op {
        Operator::Add => 2,
        Operator::Sub => 2,
        Operator::Mul => 2,
    }
}

fn eval_operator(op: Operator, args: Vec<Value>) -> Value {
    assert_eq!(args.len(), 2);
    let arg1 = match args[0] {
        Value::Int(n) => n,
        _ => unreachable!()
    };
    let arg2 = match args[1] {
        Value::Int(n) => n,
        _ => unreachable!()
    };

    let result = match op {
        Operator::Add => arg1 + arg2,
        Operator::Sub => arg1 - arg2,
        Operator::Mul => arg1 * arg2,
    };

    Value::Int(result)
}

#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Func {
        params: Vec<Pattern>,
        applied_args: Vec<Value>,
        body: Expr,
    },
    Operator {
        op: Operator,
        applied_args: Vec<Value>
    },
    Constructor {
        name: String,
        applied_args: Vec<Value>
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Func { .. } => write!(f, "<func>"),
            Value::Operator { .. } => write!(f, "<func>"),
            Value::Constructor { name, applied_args } => {
                write!(f, "{}", name)?;
                for arg in applied_args {
                    write!(f, " {}", arg)?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug)]
pub enum Error {
    ApplicationOfNonFunction,
    UndefinedVariable(String),
    InvalidMatchTarget,
    NoMatchingBranch,
}

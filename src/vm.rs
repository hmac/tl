use std::collections::HashMap;

use tracing::{debug, error};

use crate::{
    ast::{Operator, Pattern},
    compiler::{BlockId, Compiler, InstLoc, Instruction, Program},
};

/// Executes VM instructions.
pub struct Vm {
    // name => (start instruction, arg names)
    pub functions: HashMap<String, (BlockId, Vec<String>)>,
    pub prog: Program,
}

impl Vm {
    pub fn from_compiler(compiler: Compiler) -> Self {
        Self {
            functions: compiler.functions,
            prog: compiler.program,
        }
    }

    pub fn run(&self, mut block_id: BlockId) -> Result<Value, Error> {
        dbg!(&self.prog);
        dbg!(&self.functions);
        let mut block = self.prog.get_block(block_id);
        let mut ip = 0;
        let mut stack = vec![];
        // (return block, return address, stack frame index)
        let mut frames: Vec<(BlockId, InstLoc, usize)> = vec![];

        loop {
            println!("{:?}", block_id);
            println!("{ip}: {:?} - {}", &block[ip], display_value_list(&stack));
            println!("{:?}", &frames);
            match &block[ip] {
                Instruction::AddInt => match (stack.pop().unwrap(), stack.pop().unwrap()) {
                    (Value::Int(x), Value::Int(y)) => {
                        stack.push(Value::Int(x + y));
                        ip += 1;
                    }
                    (x, y) => {
                        error!(?x, ?y, "add_int: bad args");
                        panic!("add_int: bad args");
                    }
                },
                Instruction::SubInt => match (stack.pop().unwrap(), stack.pop().unwrap()) {
                    (Value::Int(x), Value::Int(y)) => {
                        stack.push(Value::Int(x - y));
                        ip += 1;
                    }
                    (x, y) => {
                        error!(?x, ?y, "sub_int: bad args");
                        panic!("sub_int: bad args");
                    }
                },
                Instruction::MulInt => match (stack.pop().unwrap(), stack.pop().unwrap()) {
                    (Value::Int(x), Value::Int(y)) => {
                        stack.push(Value::Int(x * y));
                        ip += 1;
                    }
                    (x, y) => {
                        error!(?x, ?y, "mul_int: bad args");
                        panic!("mul_int: bad args");
                    }
                },
                Instruction::Eq => {
                    let x = stack.pop().unwrap();
                    let y = stack.pop().unwrap();
                    stack.push(Value::Bool(x == y));
                    ip += 1;
                }

                Instruction::PushInt(n) => {
                    stack.push(Value::Int(*n));
                    ip += 1;
                }
                Instruction::PushGlobal(v) => {
                    let (func_block_id, args) = self.functions.get(v).unwrap();
                    let val = Value::Func {
                        name: v.to_string(),
                        num_args: args.len() as u8,
                        block_id: *func_block_id,
                        args: vec![],
                    };
                    stack.push(val);
                    ip += 1;
                }
                Instruction::PushVar(v) => {
                    // The variable is either:
                    // - local
                    // - a constructor
                    // TODO: can v be a constructor?
                    // v is an offset from the current stack frame
                    let frame_index = frames[frames.len() - 1].2;
                    let val_index = frame_index + v;
                    debug!("push_var({v}): frame_index={frame_index} val_index={val_index}");
                    let val = stack[frame_index + v].clone();

                    stack.push(val);
                    ip += 1;
                }
                Instruction::PushCtor(c) => {
                    let val = Value::Constructor {
                        name: c.to_string(),
                        args: vec![],
                    };
                    stack.push(val);
                    ip += 1;
                }
                Instruction::MakeList(len) => {
                    let mut list = Value::ListNil;
                    let mut elems = vec![];
                    for _ in 0..*len {
                        elems.push(stack.pop().expect("MakeList: empty stack"));
                    }
                    elems.reverse();
                    for e in elems {
                        list = Value::ListCons(Box::new(e), Box::new(list));
                    }
                    stack.push(list);
                    ip += 1;
                }
                Instruction::Ctor(c, len) => {
                    let mut args = stack.split_off(stack.len() - *len as usize);
                    args.reverse();
                    let val = Value::Constructor {
                        name: c.to_string(),
                        args,
                    };
                    stack.push(val);
                    ip += 1;
                }
                Instruction::Call(len) => {
                    // The top of the stack holds either a constructor or a function.
                    match stack.pop().unwrap() {
                        Value::Func {
                            name,
                            block_id: func_block_id,
                            num_args,
                            mut args,
                        } => {
                            // Check if we've saturated the function
                            debug!("func name={name} num_args={num_args}");
                            if num_args as usize == args.len() + *len as usize {
                                // Push the already-applied args onto the stack
                                for arg in args.into_iter().rev() {
                                    stack.push(arg);
                                }
                                let frame = (block_id, ip + 1, stack.len() - *len as usize);
                                frames.push(frame);
                                // Jump to the function
                                block_id = func_block_id;
                                block = self.prog.get_block(func_block_id);
                                ip = 0
                            } else {
                                // Push the new args and put the function back on the stack
                                for _ in 0..*len {
                                    args.push(stack.pop().unwrap());
                                }
                                stack.push(Value::Func {
                                    name,
                                    block_id,
                                    num_args,
                                    args,
                                });
                                ip += 1;
                            }
                        }
                        Value::Constructor { name, mut args } => {
                            // Push the new args onto the constructor
                            for _ in 0..*len {
                                args.push(stack.pop().unwrap());
                            }
                            stack.push(Value::Constructor { name, args });
                            ip += 1;
                        }
                        e => unreachable!("unexpected top of stack: {e:?} ({stack:?})"),
                    }
                }
                Instruction::TailCall => {
                    // Save the new arguments (how many?)
                    // Overwrite the current frame with new args, dropping any locals
                    // Jump to the start of the function
                }
                Instruction::Bind(_) => {
                    // Store the top of the stack in locals
                }
                Instruction::Case(branches) => {
                    // Match the top of the stack against each pattern
                    // If there's a match, jump to the corresponding location
                    let target = stack.pop().expect("case: empty stack");
                    match eval_case(&target, &branches) {
                        Some((new_block_id, bindings)) => {
                            // Push any values bound by the pattern
                            for v in bindings {
                                stack.push(v.clone());
                            }
                            // Jump to the branch
                            // We're jumping to a new block but not calling a function, so we don't
                            // push a new stack frame but we need to update the current one to
                            // record our new block id.
                            block_id = new_block_id;

                            block = self.prog.get_block(new_block_id);
                            ip = 0;
                        }
                        None => {
                            todo!("No matching case branch");
                        }
                    }
                }
                Instruction::Ret => {
                    let result = stack.pop().expect("ret: empty stack");
                    if let Some((caller_block_id, caller_addr, frame_index)) = frames.pop() {
                        stack.split_off(frame_index);
                        stack.push(result);

                        block_id = caller_block_id;
                        block = self.prog.get_block(block_id);
                        ip = caller_addr;
                    } else {
                        // We're at the top level. Return the result.
                        return Ok(result);
                    }
                }
            }
        }
    }
}

fn eval_case<'a>(
    target: &'a Value,
    branches: &[(Pattern, BlockId)],
) -> Option<(BlockId, Vec<&'a Value>)> {
    for (pattern, block_id) in branches {
        match match_pattern(target, pattern) {
            Some(bound_values) => {
                return Some((*block_id, bound_values));
            }
            None => {}
        }
    }
    None
}

fn match_pattern<'a>(target: &'a Value, pattern: &Pattern) -> Option<Vec<&'a Value>> {
    match pattern {
        Pattern::Constructor { loc, name, args } => match target {
            Value::ListCons(x, xs) => {
                if name == "Cons" {
                    match (match_pattern(x, &args[0]), match_pattern(xs, &args[1])) {
                        (Some(mut x_bound), Some(mut xs_bound)) => {
                            x_bound.append(&mut xs_bound);
                            Some(x_bound)
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            }
            Value::ListNil => {
                if name == "Nil" {
                    Some(vec![])
                } else {
                    None
                }
            }
            Value::Constructor {
                name: target_name,
                args: target_args,
            } => {
                if name == target_name {
                    assert_eq!(args.len(), target_args.len());
                    let mut bindings = vec![];
                    for (val, pattern) in target_args.iter().zip(args) {
                        if let Some(mut new_bindings) = match_pattern(val, pattern) {
                            bindings.append(&mut new_bindings);
                        } else {
                            return None;
                        }
                    }
                    Some(bindings)
                } else {
                    None
                }
            }
            _ => unreachable!(),
        },
        Pattern::Var { loc, name } => Some(vec![target]),
        Pattern::Int { loc, value } => match target {
            Value::Int(n) if n == value => Some(vec![]),
            _ => None,
        },
        Pattern::Wildcard { loc } => Some(vec![]),
    }
}

#[derive(Debug)]
pub enum Error {}

#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Bool(bool),
    ListCons(Box<Value>, Box<Value>),
    ListNil,
    Func {
        name: String,
        block_id: BlockId,
        num_args: u8,
        args: Vec<Value>,
    },
    Operator {
        op: Operator,
        applied_args: Vec<Value>,
    },
    Constructor {
        name: String,
        args: Vec<Value>,
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
                _ => unreachable!("self: {self:?} other: {other:?}"),
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
                args: args_l,
            } => match other {
                Self::Constructor {
                    name: name_r,
                    args: args_r,
                } => name_l == name_r && args_l == args_r,
                Self::ListNil => name_l == "Nil",
                Self::ListCons(arg1, arg2) => {
                    name_l == "Cons"
                        && args_l.len() == 2
                        && args_l[0] == **arg1
                        && args_l[1] == **arg2
                }
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

fn display_value_list(list: &Vec<Value>) -> String {
    let mut r = "[".to_string();
    for (i, e) in list.iter().enumerate() {
        r.push_str(&e.to_string());
        if i < list.len() - 1 {
            r.push_str(", ");
        }
    }
    r.push_str("]");
    r
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Func { block_id, .. } => write!(f, "<func({})>", block_id.0),
            Value::Operator { .. } => write!(f, "<func>"),
            Value::Constructor { name, args } => {
                write!(f, "{}", name)?;
                for arg in args {
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

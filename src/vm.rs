use std::collections::HashMap;

use tracing::error;

use crate::{
    ast::Operator,
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

    pub fn run(&self, block_id: BlockId) -> Result<Value, Error> {
        let mut block = self.prog.get_block(block_id);
        let mut ip = 0;
        let mut stack = vec![];
        // (return address, stack frame index)
        let mut frames: Vec<(InstLoc, usize)> = vec![];
        let mut locals: HashMap<String, Value> = HashMap::new();

        loop {
            println!("{:?} - {stack:?}", &block[ip]);
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
                Instruction::PushVar(v) => {
                    // The variable is either:
                    // - local
                    // - a global function
                    // - a constructor
                    let val = if let Some(val) = locals.get(v) {
                        val.clone()
                    } else {
                        if let Some((func_block_id, args)) = self.functions.get(v) {
                            Value::Func {
                                name: v.to_string(),
                                num_args: args.len() as u8,
                                block_id: *func_block_id,
                                args: vec![],
                            }
                        } else {
                            Value::Constructor {
                                name: v.to_string(),
                                args: vec![],
                            }
                        }
                    };
                    stack.push(val);
                    ip += 1;
                }
                Instruction::PushCtor(c) => {
                    todo!()
                }
                Instruction::MakeList(len) => {
                    let mut list = Value::ListNil;
                    for _ in 0..*len {
                        list = Value::ListCons(Box::new(stack.pop().unwrap()), Box::new(list));
                    }
                    stack.push(list);
                    ip += 1;
                }
                Instruction::Ctor(c, len) => {
                    let new_stack = stack.split_off(*len as usize);
                    let val = Value::Constructor {
                        name: c.to_string(),
                        args: stack,
                    };
                    stack = new_stack;
                    stack.push(val);
                    ip += 1;
                }
                Instruction::Call(len) => {
                    // The top of the stack holds either a constructor or a function.
                    match stack.pop().unwrap() {
                        Value::Func {
                            name,
                            block_id,
                            num_args,
                            mut args,
                        } => {
                            // Check if we've saturated the function
                            if num_args as usize == args.len() + *len as usize {
                                // Push the already-applied args onto the stack
                                for arg in args.into_iter().rev() {
                                    stack.push(arg);
                                }
                                let frame = (ip + 1, stack.len() - *len as usize);
                                frames.push(frame);
                                // Jump to the function
                                block = self.prog.get_block(block_id);
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
                Instruction::Case(_) => {
                    // Match the top of the stack against each pattern
                    // If there's a match, jump to the corresponding location
                }
                Instruction::Ret => {
                    let result = stack.pop().expect("ret: empty stack");
                    if let Some((ret_loc, frame_index)) = frames.pop() {
                        ip = ret_loc;
                        stack.split_off(frame_index + 1);
                    } else {
                        // We're at the top level. Return the result.
                        return Ok(result);
                    }
                }
            }
        }
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
                args: args_l,
            } => match other {
                Self::Constructor {
                    name: name_r,
                    args: args_r,
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

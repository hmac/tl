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
        let mut block = self.prog.get_block(block_id);
        let mut ip = 0;
        let mut stack = vec![];
        // (function block, return block, return address, stack frame index)
        let mut frames: Vec<(BlockId, BlockId, InstLoc, usize)> = vec![];

        // We store two block IDs in each frame: the function block and the return block.
        // On function entry these are the same, and point to the block which called the current
        // function.
        // If we then call a function from the RHS of a case expression, we want to return to the
        // correct block (the RHS) when that function returns, rather than to the original function
        // block. So before jumping we update the return address to hold the ID of the RHS block.
        // We still need the ID of the original function block to implement tail calls. That's why
        // we have both.
        let mut current_function_block_id = block_id;

        loop {
            let instruction = &block[ip];
            debug!(
                "({}) {ip}: {:?} {} {:?}",
                &block_id.0,
                instruction,
                display_value_list(&stack),
                &frames
            );
            match instruction {
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
                    debug!("push_int({n})");
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
                    debug!("push_var({v}): frames.len()={}", frames.len());
                    let frame_index = match frames.last() {
                        Some((_, _, _, i)) => *i,
                        None => 0,
                    };
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
                    let val = if c == "Cons" {
                        assert_eq!(args.len(), 2);
                        let arg1 = args.pop().unwrap();
                        let arg0 = args.pop().unwrap();
                        Value::ListCons(Box::new(arg0), Box::new(arg1))
                    } else {
                        Value::Constructor {
                            name: c.to_string(),
                            args,
                        }
                    };
                    stack.push(val);
                    ip += 1;
                }
                Instruction::Call => {
                    // The top of the stack holds either a constructor or a function.
                    let func_or_ctor = stack.pop().unwrap();

                    // The next element in the stack holds the number of args in this call
                    let len: usize = match stack.pop() {
                        Some(Value::Int(n)) => n as usize,
                        _ => unreachable!(),
                    };

                    debug!("call({len})");

                    match func_or_ctor {
                        Value::Func {
                            name,
                            block_id: func_block_id,
                            num_args,
                            mut args,
                        } => {
                            // Check if we've saturated the function
                            if num_args as usize == args.len() + len {
                                debug!(
                                    "func name={name} num_args={num_args} block_id={} (saturated)",
                                    func_block_id.0
                                );
                                // Push the already-applied args onto the stack
                                for arg in args.into_iter().rev() {
                                    stack.push(arg);
                                }
                                let frame = (
                                    current_function_block_id,
                                    block_id,
                                    ip + 1,
                                    stack.len() - num_args as usize,
                                );
                                frames.push(frame);
                                // Jump to the function
                                block_id = func_block_id;
                                current_function_block_id = func_block_id;
                                block = self.prog.get_block(func_block_id);
                                ip = 0;
                            } else {
                                if (num_args as usize) < args.len() + len {
                                    debug!(
                                        "func name={name} num_args={num_args} block_id={} (oversaturated)",
                                        func_block_id.0
                                    );
                                    // num_args may be less than args.len() + len if the function
                                    // returns another function. We handle this by:
                                    // - supplying as many args as needed to saturate the current function
                                    // - evaluating its body
                                    // - returning to here to apply the remaining args, possible
                                    //   re-evaluating if the returned function is also saturated.

                                    // After calling the function we want to return to here,
                                    // as the function will return another function that we then
                                    // want to call. However upon returning to here, `len` will be
                                    // incorrect (as it refers to the number of originally-applied
                                    // args, not the number of remaining args.
                                    // In Kite we solved this by storing `len` on the stack (via
                                    // PushInt) prior to the `Call` instruction. Maybe we want to
                                    // do the same here?

                                    // When the function returns, we want the stack to look like
                                    // argN
                                    // argN-1
                                    // ...
                                    // argM+1
                                    // len (N-M)
                                    // return value

                                    // So first we pop all the args that the called function will
                                    // use.

                                    let num_extra_args = num_args as usize - args.len();
                                    let mut extra_args = vec![];
                                    for _ in 0..num_extra_args {
                                        extra_args.push(stack.pop().unwrap());
                                    }

                                    debug!("arg len stack index: {}", stack.len());

                                    // Then we push the new len (len - num_args) onto the stack,
                                    // then push the args required to saturate the function
                                    // (arg0..argM).
                                    stack.push(Value::Int((len - num_args as usize) as i64));

                                    // Then we push the already-applied args onto the stack
                                    for arg in args.into_iter().rev() {
                                        stack.push(arg);
                                    }

                                    // Then we push the additional args supplied in this call
                                    for arg in extra_args {
                                        stack.push(arg);
                                    }

                                    debug!("arg0 stack index: {}", stack.len());

                                    // Construct the new frame
                                    let frame = (
                                        current_function_block_id,
                                        block_id,
                                        ip,
                                        stack.len() - num_args as usize,
                                    );

                                    debug!("frame: {:?}", frame);
                                    frames.push(frame);

                                    // Jump to the function
                                    block_id = func_block_id;
                                    current_function_block_id = func_block_id;
                                    block = self.prog.get_block(func_block_id);
                                    ip = 0;
                                } else {
                                    debug!("func name={name} num_args={num_args}");
                                    // Push the new args and put the function back on the stack
                                    for _ in 0..len {
                                        args.push(stack.pop().unwrap());
                                    }
                                    stack.push(Value::Func {
                                        name,
                                        block_id: func_block_id,
                                        num_args,
                                        args,
                                    });
                                    ip += 1;
                                }
                            }
                        }
                        Value::Constructor { name, mut args } => {
                            // Push the new args onto the constructor
                            for _ in 0..len {
                                args.push(stack.pop().unwrap());
                            }
                            stack.push(Value::Constructor { name, args });
                            ip += 1;
                        }
                        e => unreachable!("unexpected top of stack: {e:?} ({stack:?})"),
                    }
                }
                Instruction::TailCall => {
                    debug!("tail_call");
                    // The stack layout is the same as for a normal call instruction
                    // except the function isn't on the stack.

                    // Pop the argument length, then all the arguments.
                    let num_args = match stack.pop().unwrap() {
                        Value::Int(n) => n,
                        _ => unreachable!(),
                    };

                    let mut args = vec![];
                    for _ in 0..num_args {
                        args.push(stack.pop().unwrap());
                    }

                    let frame_index = match frames.last() {
                        Some((_, _, _, i)) => *i,
                        None => 0,
                    };

                    // Clear the stack up to the current stack frame index.
                    stack.truncate(frame_index);

                    // Push the arguments back on
                    for arg in args.into_iter().rev() {
                        stack.push(arg);
                    }

                    // Jump to the start of the current function
                    block_id = current_function_block_id;
                    block = self.prog.get_block(block_id);
                    ip = 0;
                }
                Instruction::Case(branches) => {
                    // Match the top of the stack against each pattern
                    // If there's a match, jump to the corresponding location
                    let target = stack.pop().expect("case: empty stack");
                    match eval_case(&target, &branches) {
                        Some((new_block_id, bindings)) => {
                            debug!("case: {bindings:?}");
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
                    if let Some((caller_func_block_id, caller_block_id, caller_addr, frame_index)) =
                        frames.pop()
                    {
                        debug!("ret caller_func_block_id={}, caller_block_id={} caller_addr={caller_addr} frame_index={frame_index} stack={}", caller_func_block_id.0, caller_block_id.0, display_value_list(&stack));
                        stack.truncate(frame_index);
                        stack.push(result);

                        block_id = caller_block_id;
                        block = self.prog.get_block(block_id);
                        current_function_block_id = caller_func_block_id;
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
        Pattern::Constructor { name, args, .. } => match target {
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
            Value::Bool(true) => {
                if name == "True" {
                    Some(vec![])
                } else {
                    None
                }
            }
            Value::Bool(false) => {
                if name == "False" {
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
            _ => unreachable!("pattern={pattern:?} target={target:?}"),
        },
        Pattern::Var { .. } => Some(vec![target]),
        Pattern::Int { value, .. } => match target {
            Value::Int(n) if n == value => Some(vec![]),
            _ => None,
        },
        Pattern::Wildcard { .. } => Some(vec![]),
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
    // TODO: can we remove this?
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
                _ => unreachable!("self: {self:?} other: {other:?}"),
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
            Value::Func { block_id, name, .. } => write!(f, "<func({}: {name})>", block_id.0),
            Value::Operator { .. } => write!(f, "<func(op)>"),
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

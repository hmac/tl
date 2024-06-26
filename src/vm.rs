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
            if ip >= block.len() {
                dbg!(ip, &block, &stack, &frames);
            }
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
                Instruction::LtInt => match (stack.pop().unwrap(), stack.pop().unwrap()) {
                    (Value::Int(x), Value::Int(y)) => {
                        stack.push(Value::Bool(x < y));
                        ip += 1;
                    }
                    (x, y) => {
                        error!(?x, ?y, "lt_int: bad args");
                        panic!("lt_int: bad args");
                    }
                },
                Instruction::Eq => {
                    let x = stack.pop().unwrap();
                    let y = stack.pop().unwrap();
                    stack.push(Value::Bool(x == y));
                    ip += 1;
                }
                // Convert the string (top of stack) into a list of characters
                Instruction::Chars => {
                    let s = stack.pop().unwrap();
                    match s {
                        Value::Str(s) => {
                            let elems = s.chars().rev();
                            let mut list = Value::ListNil;
                            for e in elems {
                                list = Value::ListCons(Box::new(Value::Char(e)), Box::new(list));
                            }
                            stack.push(list);
                            ip += 1;
                        }
                        _ => unreachable!("chars: arg is not a string"),
                    }
                }
                // Return the character at a specific index in the string.
                // If n is out of range, it loops around, so always returns a character.
                Instruction::CharAt => {
                    let index = stack.pop().unwrap();
                    let s = stack.pop().unwrap();
                    match s {
                        Value::Str(s) => match index {
                            Value::Int(n) => {
                                let char = s.chars().cycle().nth(n as usize).unwrap();
                                stack.push(Value::Char(char));
                                ip += 1;
                            }
                            _ => unreachable!("char_at: first arg is not an int"),
                        },
                        _ => unreachable!("char_at: second arg is not a string"),
                    }
                }

                Instruction::PushInt(n) => {
                    debug!("push_int({n})");
                    stack.push(Value::Int(*n));
                    ip += 1;
                }
                Instruction::PushStr(s) => {
                    debug!("push_str({s})");
                    stack.push(Value::Str(s.to_string()));
                    ip += 1;
                }
                Instruction::PushChar(c) => {
                    debug!("push_char({c})");
                    stack.push(Value::Char(*c));
                    ip += 1;
                }
                Instruction::PushBool(b) => {
                    debug!("push_bool({b})");
                    stack.push(Value::Bool(*b));
                    ip += 1;
                }
                Instruction::PushGlobal(v) => {
                    if self.functions.get(v).is_none() {
                        dbg!(&self.functions);
                        dbg!(&v);
                    }
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
                    if stack.len() <= frame_index + v {
                        dbg!(current_function_block_id);
                        dbg!(block_id);
                        dbg!(&frames);
                        dbg!(&stack);
                    }
                    let val = stack[frame_index + v].clone();

                    stack.push(val);
                    ip += 1;
                }
                Instruction::PushCtor(c) => {
                    let val = if c == "Nil" {
                        Value::ListNil
                    } else {
                        Value::Constructor {
                            name: c.to_string(),
                            args: vec![],
                        }
                    };
                    stack.push(val);
                    ip += 1;
                }
                // We expect that the top `len` elements on the stack are the list elements, and
                // the `len + 1`th element is the final element, which is often Nil.
                Instruction::MakeList(len) => {
                    let mut elems = vec![];
                    for _ in 0..*len {
                        elems.push(stack.pop().expect("MakeList: empty stack"));
                    }
                    let mut list = stack.pop().expect("MakeList: empty stack");
                    elems.reverse();
                    for e in elems {
                        list = Value::ListCons(Box::new(e), Box::new(list));
                    }
                    stack.push(list);
                    ip += 1;
                }
                Instruction::MakeTuple(len) => {
                    let mut elems = vec![];
                    for _ in 0..*len {
                        elems.push(stack.pop().expect("MakeTuple: empty stack"));
                    }
                    stack.push(Value::Tuple(elems));
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
                        Some((jump_amount, bindings)) => {
                            debug!("case: {target:?} {bindings:?}");
                            // Push any values bound by the pattern
                            for v in bindings {
                                stack.push(v.clone());
                            }

                            // Jump forward to the branch
                            ip += jump_amount;
                        }
                        None => {
                            // TODO: flesh out this error
                            return Err(Error::NoMatchingBranch);
                        }
                    }
                }
                Instruction::Jump(amount) => {
                    debug!("jmp {amount}");
                    ip += amount;
                }
                Instruction::Ret => {
                    let result = stack.pop().expect("ret: empty stack");
                    if let Some((caller_func_block_id, caller_block_id, caller_addr, frame_index)) =
                        frames.pop()
                    {
                        debug!("ret caller_func_block_id={}, caller_block_id={} caller_addr={caller_addr} frame_index={frame_index} stack={} result={result}", caller_func_block_id.0, caller_block_id.0, display_value_list(&stack));
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
                Instruction::Shift(n) => {
                    let result = stack.pop().expect("shift: empty stack");
                    if stack.len() < *n {
                        panic!("shift({n}): stack too small ({})", stack.len())
                    }
                    for _ in 0..*n {
                        stack.pop().unwrap();
                    }
                    stack.push(result);
                    ip += 1
                }
            }
        }
    }
}

/// Return the jump amount and new bound vars for the case instruction, if any.
fn eval_case<'a>(
    target: &'a Value,
    branches: &[(Pattern, usize)],
) -> Option<(usize, Vec<&'a Value>)> {
    for (pattern, jump_amount) in branches {
        match match_pattern(target, pattern) {
            Some(bound_values) => {
                return Some((*jump_amount, bound_values));
            }
            None => {}
        }
    }
    None
}

fn match_pattern<'a>(target: &'a Value, pattern: &Pattern) -> Option<Vec<&'a Value>> {
    match pattern {
        Pattern::Constructor { name, args, .. } => match target {
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
        Pattern::ListNil { .. } => {
            if *target == Value::ListNil {
                Some(vec![])
            } else {
                None
            }
        }
        Pattern::ListCons { elems, tail, .. } => match target {
            Value::ListCons(x, xs_) => {
                if elems.is_empty() {
                    None
                } else {
                    let mut xs: &Value = &xs_;
                    // Match x with the first pattern in `elems`
                    let p1 = &elems[0];
                    let mut elem_matches = match_pattern(x, &p1)?;
                    // Match each element in `xs` with the coresponding patterns in `elems`
                    for p in elems.iter().skip(1) {
                        match xs {
                            Value::ListCons(y, ys) => {
                                elem_matches.append(&mut match_pattern(&*y, &p)?);
                                xs = &ys;
                            }
                            _ => {
                                return None;
                            }
                        }
                    }
                    // Match the remaining `xs` with `tail`, if it exists.
                    // Otherwise, match `xs` with ListNil
                    if let Some(tail) = tail {
                        elem_matches.append(&mut match_pattern(&*xs, &tail)?);
                    } else {
                        if *xs != Value::ListNil {
                            return None;
                        }
                    }
                    Some(elem_matches)
                }
            }
            _ => None,
        },
        Pattern::Tuple { elems, .. } => match target {
            Value::Tuple(xs) => {
                // Match each element in `xs` with the coresponding pattern in `elems`
                let mut matches = vec![];
                for (p, x) in elems.iter().zip(xs.iter()) {
                    matches.append(&mut match_pattern(x, p)?);
                }
                Some(matches)
            }
            _ => None,
        },
    }
}

#[derive(Debug)]
pub enum Error {
    UndefinedVariable(String),
    // TODO
    NoMatchingBranch,
}

#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Str(String),
    Char(char),
    Bool(bool),
    Tuple(Vec<Value>),
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
    /// Returns false if you try to compare functions (should it panic?)
    fn eq(&self, other: &Value) -> bool {
        match self {
            Self::Func { .. } => false,
            Self::Int(n) => match other {
                Self::Int(m) => n == m,
                _ => unreachable!("self: {self:?} other: {other:?}"),
            },
            Self::Str(s1) => match other {
                Self::Str(s2) => s1 == s2,
                _ => unreachable!("self: {self:?} other: {other:?}"),
            },
            Self::Char(c1) => match other {
                Self::Char(c2) => c1 == c2,
                _ => unreachable!("self: {self:?} other: {other:?}"),
            },
            Self::Bool(n) => match other {
                Self::Bool(m) => n == m,
                _ => unreachable!("self: {self:?} other: {other:?}"),
            },
            Self::Tuple(elems1) => match other {
                Self::Tuple(elems2) => elems1 == elems2,
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
            Value::Str(s) => write!(f, "\"{}\"", s),
            Value::Char(c) => write!(f, "'{c}'"),
            Value::Bool(true) => write!(f, "True"),
            Value::Bool(false) => write!(f, "False"),
            Value::Func { block_id, name, .. } => write!(f, "<func({}: {name})>", block_id.0),
            Value::Operator { .. } => write!(f, "<func(op)>"),
            Value::Constructor { name, args } => {
                write!(f, "{}", name)?;
                for arg in args {
                    write!(f, " ")?;
                    display_constructor_arg(f, arg)?;
                }
                Ok(())
            }
            Value::ListCons(head, tail) => display_nonempty_list(f, &head, &tail),
            Value::ListNil => write!(f, "[]"),
            Value::Tuple(elems) => {
                if elems.is_empty() {
                    write!(f, "(,)")
                } else {
                    write!(f, "({},", elems[0])?;
                    let n = elems.len();
                    for (i, e) in elems.iter().enumerate().skip(1) {
                        if i == n - 1 {
                            write!(f, " {})", e)?;
                        } else {
                            write!(f, " {}, ", e)?;
                        }
                    }
                    write!(f, ")")
                }
            }
        }
    }
}

fn display_constructor_arg(
    f: &mut std::fmt::Formatter<'_>,
    arg: &Value,
) -> Result<(), std::fmt::Error> {
    match arg {
        Value::Constructor { args, .. } if args.len() > 0 => write!(f, "({})", arg),
        _ => write!(f, "{}", arg),
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
            t => unreachable!("{:?}", t),
        }
    }
    write!(f, "]")
}

use std::collections::HashMap;

use tracing::debug;

use crate::ast::{Expr, Loc, Operator, Pattern, Var};

/// Compiles expressions to VM instructions
pub struct Compiler {
    pub program: Program,
    // name => (start instruction, arg names)
    pub functions: HashMap<String, (BlockId, Vec<String>)>,
    rng: tinyrand::StdRand,
}

impl Compiler {
    pub fn new() -> Self {
        let mut _self = Self {
            program: Program::new(),
            functions: HashMap::new(),
            rng: tinyrand::StdRand::default(),
        };

        _self.compile_operators();

        _self
    }

    pub fn compile_func(&mut self, name: &str, body: &Expr) -> Result<(), Error> {
        // If the body is a function, compile it without an additional lambda lift
        // This prevents e.g.
        //
        // f { x -> x }
        //
        // becoming
        //
        // f: push_var x; push_var func_1234; call 1
        // func_1234: push_var x; ret
        //
        // instead we get
        //
        // f: push_var x; ret

        let (ins, args) = match body {
            Expr::Func { args, body, .. } => {
                let mut locals = Vec::new();
                for (_, a) in args.iter().rev() {
                    locals.push(a.to_string());
                }
                let ins = self.compile_expr(name, body, locals, true)?;
                (ins, args.iter().map(|(_, n)| n.to_string()).collect())
            }
            e => (self.compile_expr(name, e, Vec::new(), true)?, vec![]),
        };
        let id = self.program.add_block(ins);
        self.functions.insert(name.to_string(), (id, args));
        Ok(())
    }

    fn compile_expr(
        &mut self,
        func_name: &str,
        expr: &Expr,
        locals: Vec<String>,
        // true if expr is a leaf node of the function body. This tells us if we need to insert a
        // 'ret' instruction.
        is_leaf: bool,
    ) -> Result<Vec<Instruction>, Error> {
        let mut ins = vec![];
        match expr {
            Expr::Var(_, Var::Local(v)) => {
                // Find the innermost matching variable in locals
                match locals.iter().enumerate().find(|(_, x)| x == &v) {
                    Some((index, _)) => {
                        ins.push(Instruction::PushVar(index));
                    }
                    None => {
                        // Call the global to ensure it is evaluated to normal form
                        ins.push(Instruction::PushInt(0));
                        ins.push(Instruction::PushGlobal(v.to_string()));
                        ins.push(Instruction::Call);
                    }
                }
            }
            Expr::Var(_, Var::Constructor(c)) => {
                debug!("{:?}", c);
                ins.push(Instruction::PushCtor(c.clone()));
            }
            Expr::Var(_, Var::Operator(op)) => {
                ins.push(match op {
                    Operator::Add => Instruction::PushGlobal("+".to_string()),
                    Operator::Sub => Instruction::PushGlobal("-".to_string()),
                    Operator::Mul => Instruction::PushGlobal("*".to_string()),
                    Operator::Lt => Instruction::PushGlobal("<".to_string()),
                    Operator::Eq => Instruction::PushGlobal("==".to_string()),
                });
            }
            Expr::Int(_, i) => {
                ins.push(Instruction::PushInt(*i));
            }
            Expr::Str(_, s) => {
                ins.push(Instruction::PushStr(s.to_string()));
            }
            Expr::Char(_, c) => {
                ins.push(Instruction::PushChar(*c));
            }
            Expr::List { elems, tail, .. } => {
                assert!(elems.len() <= (u8::MAX as usize));
                // Compile the tail expression, if present
                // Otherwise push Nil
                if let Some(tail) = tail {
                    ins.append(&mut self.compile_expr(func_name, tail, locals.clone(), false)?);
                } else {
                    ins.push(Instruction::PushCtor("Nil".to_string()));
                }
                for e in elems.iter().rev() {
                    ins.append(&mut self.compile_expr(func_name, e, locals.clone(), false)?);
                }
                ins.push(Instruction::MakeList(elems.len() as u8));
            }
            Expr::Tuple { elems, .. } => {
                assert!(elems.len() <= (u8::MAX as usize));
                for e in elems.iter().rev() {
                    ins.append(&mut self.compile_expr(func_name, e, locals.clone(), false)?);
                }
                ins.push(Instruction::MakeTuple(elems.len() as u8));
            }
            Expr::Case {
                target, branches, ..
            } => {
                ins.append(&mut self.compile_expr(func_name, target, locals.clone(), false)?);
                // Compile each branch, and determine their start locations
                let mut pattern_locs = vec![];
                for branch in branches {
                    let mut locals = locals.clone();
                    // TODO: add pattern bindings to locals
                    for var in branch.pattern.ordered_vars() {
                        locals.push(var);
                    }
                    let branch_ins = self.compile_expr(func_name, &branch.rhs, locals, is_leaf)?;
                    let branch_id = self.program.add_block(branch_ins);
                    pattern_locs.push((branch.pattern.clone(), branch_id));
                }
                let case = Instruction::Case(pattern_locs);
                ins.push(case);
            }
            Expr::Func { args, body, .. } => {
                // Lift the function, then apply any captured variables
                let name = self.lift_func(&locals, args, body)?;
                for (i, _) in locals.iter().enumerate() {
                    ins.push(Instruction::PushVar(i));
                }
                ins.push(Instruction::PushInt(locals.len() as i64));
                ins.push(Instruction::PushGlobal(name));
                ins.push(Instruction::Call);
            }
            Expr::App { head, args, .. } => {
                // Examine head
                // If it is a constructor, use Ctor
                // If it is a local variable, use call
                // If it is a function literal, lambda lift it
                // If it is a complex expression, compile that first
                match &**head {
                    Expr::Var(_, Var::Constructor(c)) => {
                        debug!("head: {:?}", c);
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(
                                func_name,
                                a,
                                locals.clone(),
                                false,
                            )?);
                        }
                        ins.push(Instruction::Ctor(c.clone(), args.len() as u8));
                    }
                    Expr::Var(_, Var::Local(v)) => {
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(
                                func_name,
                                a,
                                locals.clone(),
                                false,
                            )?);
                        }

                        ins.push(Instruction::PushInt(args.len() as i64));

                        // Check if the variable is local or global
                        let local_var_index = locals
                            .iter()
                            .enumerate()
                            .find(|(_, x)| x == &v)
                            .map(|(i, _)| i);

                        // If we're doing a tail call, use the TailCall instruction
                        if is_leaf && v == func_name && local_var_index.is_none() {
                            ins.push(Instruction::TailCall);
                        } else {
                            ins.push(match local_var_index {
                                Some(index) => Instruction::PushVar(index),
                                None => Instruction::PushGlobal(v.clone()),
                            });
                            ins.push(Instruction::Call);
                        }
                    }
                    Expr::Var(_, Var::Operator(o)) => {
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(
                                func_name,
                                a,
                                locals.clone(),
                                false,
                            )?);
                        }
                        ins.push(match o {
                            Operator::Add => Instruction::AddInt,
                            Operator::Sub => Instruction::SubInt,
                            Operator::Mul => Instruction::MulInt,
                            Operator::Lt => Instruction::LtInt,
                            Operator::Eq => Instruction::Eq,
                        });
                    }
                    _ => todo!(),
                }
            }
            Expr::Let { bindings, body, .. } => {
                let mut locals = locals.clone();
                for b in bindings {
                    ins.append(&mut self.compile_expr(
                        func_name,
                        &b.value,
                        locals.clone(),
                        false,
                    )?);
                    locals.push(b.name.to_string());
                }
                ins.append(&mut self.compile_expr(func_name, body, locals, is_leaf)?);
            }
        };
        if is_leaf {
            ins.push(Instruction::Ret);
        }
        Ok(ins)
    }

    fn generate_fresh_name(&mut self) -> String {
        use tinyrand::Rand;

        format!("{}", self.rng.next_u16())
    }

    fn lift_func(
        &mut self,
        locals: &Vec<String>,
        args: &[(Loc, String)],
        body: &Expr,
    ) -> Result<String, Error> {
        // The lifted function takes all its original arguments, plus any (captured?)
        // local variables. The captured variables come first.
        // When the function is called, arguments are pushed onto the stack in reverse order,
        // so the body's locals are [argN, argN-1, ... arg1, capturedN, capturedN-1, ..., captured1]
        let mut body_locals = locals.clone();
        body_locals.reverse();
        for (_, v) in args {
            body_locals.push(v.to_string())
        }
        let name = self.generate_fresh_name();
        let ins = self.compile_expr(
            &name,
            body,
            {
                let mut locals = body_locals.clone();
                locals.reverse();
                locals
            },
            true,
        )?;
        let block_id = self.program.add_block(ins);
        self.functions
            .insert(name.clone(), (block_id, body_locals.to_vec()));
        Ok(name)
    }

    fn compile_operators(&mut self) {
        // Compile an instruction sequence for each operator so they can be used as first-class
        // functions.
        self.compile_func(
            "+",
            &Expr::Func {
                loc: (0, 0),
                args: vec![((0, 0), "x".to_string()), ((0, 0), "y".to_string())],
                body: Box::new(Expr::App {
                    loc: (0, 0),
                    head: Box::new(Expr::Var((0, 0), Var::Operator(Operator::Add))),
                    args: vec![
                        Expr::Var((0, 0), Var::Local("x".to_string())),
                        Expr::Var((0, 0), Var::Local("y".to_string())),
                    ],
                }),
            },
        )
        .unwrap();
        self.compile_func(
            "-",
            &Expr::Func {
                loc: (0, 0),
                args: vec![((0, 0), "x".to_string()), ((0, 0), "y".to_string())],
                body: Box::new(Expr::App {
                    loc: (0, 0),
                    head: Box::new(Expr::Var((0, 0), Var::Operator(Operator::Sub))),
                    args: vec![
                        Expr::Var((0, 0), Var::Local("x".to_string())),
                        Expr::Var((0, 0), Var::Local("y".to_string())),
                    ],
                }),
            },
        )
        .unwrap();
        self.compile_func(
            "*",
            &Expr::Func {
                loc: (0, 0),
                args: vec![((0, 0), "x".to_string()), ((0, 0), "y".to_string())],
                body: Box::new(Expr::App {
                    loc: (0, 0),
                    head: Box::new(Expr::Var((0, 0), Var::Operator(Operator::Mul))),
                    args: vec![
                        Expr::Var((0, 0), Var::Local("x".to_string())),
                        Expr::Var((0, 0), Var::Local("y".to_string())),
                    ],
                }),
            },
        )
        .unwrap();
        self.compile_func(
            "<",
            &Expr::Func {
                loc: (0, 0),
                args: vec![((0, 0), "x".to_string()), ((0, 0), "y".to_string())],
                body: Box::new(Expr::App {
                    loc: (0, 0),
                    head: Box::new(Expr::Var((0, 0), Var::Operator(Operator::Lt))),
                    args: vec![
                        Expr::Var((0, 0), Var::Local("x".to_string())),
                        Expr::Var((0, 0), Var::Local("y".to_string())),
                    ],
                }),
            },
        )
        .unwrap();
        self.compile_func(
            "==",
            &Expr::Func {
                loc: (0, 0),
                args: vec![((0, 0), "x".to_string()), ((0, 0), "y".to_string())],
                body: Box::new(Expr::App {
                    loc: (0, 0),
                    head: Box::new(Expr::Var((0, 0), Var::Operator(Operator::Eq))),
                    args: vec![
                        Expr::Var((0, 0), Var::Local("x".to_string())),
                        Expr::Var((0, 0), Var::Local("y".to_string())),
                    ],
                }),
            },
        )
        .unwrap();
    }
}

pub type InstLoc = usize;

/// A VM instruction
#[derive(Debug)]
pub enum Instruction {
    AddInt,
    SubInt,
    MulInt,
    LtInt,
    Eq,
    PushInt(i64),
    PushStr(String),
    PushChar(char),
    // Push a local variable on to the stack.
    // The argument is an offset from the stack frame index indicating the location of the variable
    // on the stack.
    // Arguments are pushed onto the stack in reverse order, so index 0 will correspond to the last
    // function argument.
    // Index 1 will be the next-to-last argument, etc.
    // After all args, the next index will be the first let-bound or case-bound variable.
    // This ensures that variable indices do not change as we evaluate a function.
    PushVar(usize),
    PushGlobal(String),
    PushCtor(String),
    MakeList(u8),
    MakeTuple(u8),
    Ctor(String, u8),
    // At the time of execution of Call, the topmost stack element must the function to call,
    // and the next element must be the number of args being provided to the call.
    // After that, the next elements on the stack should be the arguments.
    Call,
    TailCall,
    Case(Vec<(Pattern, BlockId)>),
    Ret,
}

#[derive(Debug)]
pub enum Error {}

#[derive(Debug, Clone, Copy)]
pub struct BlockId(pub usize);

#[derive(Debug)]
pub struct Program {
    blocks: Vec<Vec<Instruction>>,
}

impl Program {
    pub fn new() -> Self {
        Self { blocks: vec![] }
    }

    pub fn add_block(&mut self, block: Vec<Instruction>) -> BlockId {
        self.blocks.push(block);
        BlockId(self.blocks.len() - 1)
    }

    pub fn get_block(&self, block_id: BlockId) -> &[Instruction] {
        self.blocks[block_id.0].as_slice()
    }
}

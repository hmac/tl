use std::collections::{HashMap, HashSet};

use crate::ast::{Expr, Loc, Operator, Pattern, Var};

/// Compiles expressions to VM instructions
pub struct Compiler {
    pub program: Program,
    // name => (start instruction, arg names)
    pub functions: HashMap<String, (BlockId, Vec<String>)>,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            program: Program::new(),
            functions: HashMap::new(),
        }
    }

    pub fn compile_func(&mut self, name: &str, body: &Expr) -> Result<(), Error> {
        dbg!(body);
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

        let (mut ins, args) = match body {
            Expr::Func { args, body, .. } => {
                let ins = self.compile_expr(body, HashSet::new(), true)?;
                (ins, args.iter().map(|(_, n)| n.to_string()).collect())
            }
            e => (self.compile_expr(e, HashSet::new(), true)?, vec![]),
        };
        let id = self.program.add_block(ins);
        self.functions.insert(name.to_string(), (id, args));
        dbg!(&self.program);
        Ok(())
    }

    fn compile_expr(
        &mut self,
        expr: &Expr,
        locals: HashSet<String>,
        // true if expr is a leaf node of the function body. This tells us if we need to insert a
        // 'ret' instruction.
        is_leaf: bool,
    ) -> Result<Vec<Instruction>, Error> {
        let mut ins = vec![];
        match expr {
            Expr::Var(_, Var::Local(v)) => {
                ins.push(Instruction::PushVar(v.clone()));
            }
            Expr::Var(_, Var::Constructor(c)) => {
                ins.push(Instruction::PushCtor(c.clone()));
            }
            Expr::Var(_, Var::Operator(op)) => {
                ins.push(match op {
                    Operator::Add => Instruction::AddInt,
                    Operator::Sub => Instruction::SubInt,
                    Operator::Mul => Instruction::MulInt,
                    Operator::Eq => Instruction::Eq,
                });
            }
            Expr::Int(_, i) => {
                ins.push(Instruction::PushInt(*i));
            }
            Expr::List(_, elems) => {
                assert!(elems.len() <= (u8::MAX as usize));
                for e in elems.iter().rev() {
                    ins.append(&mut self.compile_expr(e, locals.clone(), false)?);
                }
                ins.push(Instruction::MakeList(elems.len() as u8));
            }
            Expr::Case {
                target, branches, ..
            } => {
                ins.append(&mut self.compile_expr(target, locals.clone(), false)?);
                // Compile each branch, and determine their start locations
                let mut pattern_locs = vec![];
                for branch in branches {
                    let branch_ins = self.compile_expr(&branch.rhs, locals.clone(), is_leaf)?;
                    let branch_id = self.program.add_block(branch_ins);
                    pattern_locs.push((branch.pattern.clone(), branch_id));
                }
                let case = Instruction::Case(pattern_locs);
                ins.push(case);
            }
            Expr::Func { loc, args, body } => {
                let name = self.lift_func(&locals, args, body)?;
                ins.push(Instruction::PushVar(name));
            }
            Expr::App { loc, head, args } => {
                // Examine head
                // If it is a constructor, use Ctor
                // If it is a local variable, use call
                // If it is a function literal, lambda lift it
                // If it is a complex expression, compile that first
                match &**head {
                    Expr::Var(_, Var::Constructor(c)) => {
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(a, locals.clone(), false)?);
                        }
                        ins.push(Instruction::Ctor(c.clone(), args.len() as u8));
                    }
                    Expr::Var(_, Var::Local(v)) => {
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(a, locals.clone(), false)?);
                        }
                        ins.push(Instruction::PushVar(v.clone()));
                        ins.push(Instruction::Call(args.len() as u8));
                    }
                    Expr::Var(_, Var::Operator(o)) => {
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(a, locals.clone(), false)?);
                        }
                        ins.push(match o {
                            Operator::Add => Instruction::AddInt,
                            Operator::Sub => Instruction::SubInt,
                            Operator::Mul => Instruction::MulInt,
                            Operator::Eq => Instruction::Eq,
                        });
                    }
                    Expr::Int(_, _) => todo!(),
                    Expr::List(_, _) => todo!(),
                    Expr::Case {
                        loc,
                        target,
                        branches,
                    } => todo!(),
                    Expr::Func { loc, args, body } => todo!(),
                    Expr::App { loc, head, args } => todo!(),
                    Expr::Let {
                        loc,
                        bindings,
                        body,
                    } => todo!(),
                }
            }
            Expr::Let { bindings, body, .. } => {
                let mut locals = locals.clone();
                for b in bindings {
                    ins.append(&mut self.compile_expr(&b.value, locals.clone(), false)?);
                    locals.insert(b.name.to_string());
                    ins.push(Instruction::Bind(b.name.clone()));
                }
                ins.append(&mut self.compile_expr(body, locals, is_leaf)?);
            }
        };
        if is_leaf {
            ins.push(Instruction::Ret);
        }
        Ok(ins)
    }

    fn generate_fresh_name(&self) -> String {
        use tinyrand::Rand;

        format!("{}", tinyrand::StdRand::default().next_u16())
    }

    fn lift_func(
        &mut self,
        locals: &HashSet<String>,
        args: &[(Loc, String)],
        body: &Expr,
    ) -> Result<String, Error> {
        let mut all_args: Vec<String> = args.iter().map(|(_, n)| n.to_string()).collect();
        // TODO: locals need to be a predictable order
        for l in locals {
            all_args.push(l.to_string());
        }
        let ins = self.compile_expr(body, HashSet::new(), true)?;
        let block_id = self.program.add_block(ins);
        let name = self.generate_fresh_name();
        self.functions.insert(name.clone(), (block_id, all_args));
        Ok(name)
    }
}

pub type InstLoc = usize;

/// A VM instruction
#[derive(Debug)]
pub enum Instruction {
    AddInt,
    SubInt,
    MulInt,
    Eq,
    PushInt(i64),
    PushVar(String),
    PushCtor(String),
    MakeList(u8),
    Ctor(String, u8),
    Call(u8),
    TailCall,
    Bind(String),
    Case(Vec<(Pattern, BlockId)>),
    Ret,
}

pub enum Error {}

#[derive(Debug, Clone, Copy)]
pub struct BlockId(usize);

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

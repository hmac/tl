use std::{collections::HashMap, path::Path};

use tracing::debug;

use crate::{
    ast::{Expr, GlobalName, Loc, Operator, Pattern, Var},
    typechecker::Imports,
};

/// Compiles expressions to VM instructions
pub struct Compiler {
    pub program: Program,
    // name => (start instruction, arg names)
    pub functions: HashMap<String, (BlockId, Vec<String>)>,
    rng: tinyrand::StdRand,
    imports: Imports,
}

impl Compiler {
    pub fn new(imports: Imports) -> Self {
        let mut _self = Self {
            program: Program::new(),
            functions: HashMap::new(),
            rng: tinyrand::StdRand::default(),
            imports,
        };

        // Invent a fake path to compile operators
        // TODO: fix it so we don't need to do this
        _self.compile_operators(Path::new("builtin"));

        _self
    }

    pub fn compile_func(&mut self, path: &Path, name: &str, body: &Expr) -> Result<(), Error> {
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
                let ins = self.compile_expr(path, name, body, locals, true)?;
                (ins, args.iter().map(|(_, n)| n.to_string()).collect())
            }
            e => (self.compile_expr(path, name, e, Vec::new(), true)?, vec![]),
        };
        let id = self.program.add_block(name, ins);
        let name = GlobalName::named(path, name);
        self.functions.insert(name.to_string(), (id, args));
        Ok(())
    }

    fn compile_expr(
        &mut self,
        path: &Path,
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
                        let name = GlobalName::named(path, v);
                        ins.push(Instruction::PushGlobal(name.to_string()));
                        ins.push(Instruction::Call);
                    }
                }
            }
            Expr::Var(loc, Var::Global(namespace, name)) => {
                // Look up the global's name
                let global_name = self.imports.lookup(*loc, path, namespace, name).unwrap();
                // Call the global to ensure it is evaluated to normal form
                ins.push(Instruction::PushInt(0));
                ins.push(Instruction::PushGlobal(global_name.to_string()));
                ins.push(Instruction::Call);
            }
            Expr::Var(_, Var::Constructor(_ns, c)) => {
                debug!("{:?}", c);
                ins.push(Instruction::PushCtor(c.clone()));
            }
            Expr::Var(_, Var::Operator(op)) => {
                let op_name = match op {
                    Operator::Add => "+",
                    Operator::Sub => "-",
                    Operator::Mul => "*",
                    Operator::Lt => "<",
                    Operator::Eq => "==",
                    Operator::Chars => "chars",
                    Operator::CharAt => "char_at",
                };
                ins.push(Instruction::PushGlobal(format!("builtin:{op_name}")));
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
            Expr::Bool(_, b) => {
                ins.push(Instruction::PushBool(*b));
            }
            Expr::List { elems, tail, .. } => {
                assert!(elems.len() <= (u8::MAX as usize));
                // Compile the tail expression, if present
                // Otherwise push Nil
                if let Some(tail) = tail {
                    ins.append(&mut self.compile_expr(
                        path,
                        func_name,
                        tail,
                        locals.clone(),
                        false,
                    )?);
                } else {
                    ins.push(Instruction::PushCtor("Nil".to_string()));
                }
                for e in elems.iter().rev() {
                    ins.append(&mut self.compile_expr(
                        path,
                        func_name,
                        e,
                        locals.clone(),
                        false,
                    )?);
                }
                ins.push(Instruction::MakeList(elems.len() as u8));
            }
            Expr::Tuple { elems, .. } => {
                assert!(elems.len() <= (u8::MAX as usize));
                for e in elems.iter().rev() {
                    ins.append(&mut self.compile_expr(
                        path,
                        func_name,
                        e,
                        locals.clone(),
                        false,
                    )?);
                }
                ins.push(Instruction::MakeTuple(elems.len() as u8));
            }
            Expr::Case {
                target, branches, ..
            } => {
                ins.append(&mut self.compile_expr(
                    path,
                    func_name,
                    target,
                    locals.clone(),
                    false,
                )?);
                // Case expressions are compiled as a Case instruction followed by instruction
                // sequences for each branch. At the end of each branch is a jump to the instruction
                // sequence for the parent expression of the branch. For example, consider this function:

                // f : Int { let n = case + 1 2 { x -> + x 2, _ -> 5 } { + n 1 }  }

                // This is compiled to

                // 0: push_int 2                       ; target
                // 1: push_int 1
                // 2: add
                // 3: case { int(3) -> 1, wild -> 5 }  ; case instruction - relative jumps
                // 4: push_var 0                       ; branch 1 (x)
                // 5: push_int 2
                // 6: add
                // 7: jmp 3                            ; relative jump
                // 8: push_int 5                       ; branch 2 (_)
                // 9: jmp 1                            ; relative jump
                // 10: push_var 0                      ; + n 1
                // 11: push_int 1
                // 12: add
                // 13: ret

                // We must ensure that, when leaving the case, we do not leave any local branch variables
                // on the stack. This is because the number of local variables introduced may differ between
                // branches and so later code will not have a consistent view of the stack and we will get
                // our variables muddled.
                // To deal with this, at the end of a branch and just before jumping, we remove from the stack
                // all variables pushed in the branch, leaving just the return value on top.
                // We add a specific instruction for this, called SHIFT.
                // SHIFT N removes elements 1 to N-1 from the stack, leaving element 0 on top.
                // At the end of a branch, we must SHIFT each variable that was bound by the branch pattern.

                let mut pattern_locs = vec![];
                let mut branch_instruction_sequences: Vec<Vec<Instruction>> = vec![];
                for branch in branches {
                    let mut locals = locals.clone();
                    let pattern_vars = branch.pattern.ordered_vars();
                    let pattern_var_len = pattern_vars.len();
                    for var in pattern_vars {
                        locals.push(var);
                    }
                    let mut branch_ins =
                        self.compile_expr(path, func_name, &branch.rhs, locals, false)?;
                    // SHIFT the branch pattern-bound locals off the stack before jumping
                    branch_ins.push(Instruction::Shift(pattern_var_len));
                    let case_relative_jump = branch_instruction_sequences
                        .iter()
                        .map(|ins| ins.len() + 1) // + 1 to account for the final jump instruction, not yet added
                        .sum::<usize>()
                        + 1;
                    pattern_locs.push((branch.pattern.clone(), case_relative_jump));
                    branch_instruction_sequences.push(branch_ins);
                }

                // Add a relative jump at the end of each branch instruction sequence which jumps to the
                // instruction after the last branch.
                // This is equal to the summed length of all the subsequent branch instruction sequences.

                let sequence_lengths: Vec<usize> = branch_instruction_sequences
                    .iter()
                    .map(|ins| ins.len() + 1) // + 1 to account for the final jump instruction, not yet added
                    .collect();
                for (i, seq) in branch_instruction_sequences.iter_mut().enumerate() {
                    let amount: usize = sequence_lengths.iter().skip(i + 1).sum::<usize>() + 1;
                    seq.push(Instruction::Jump(amount));
                }
                let case = Instruction::Case(pattern_locs);
                ins.push(case);
                for mut seq in branch_instruction_sequences {
                    ins.append(&mut seq);
                }
            }
            Expr::Func { args, body, .. } => {
                // Lift the function, then apply any captured variables
                let name = self.lift_func(path, &locals, args, body)?;
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
                    Expr::Var(_, Var::Constructor(_ns, c)) => {
                        debug!("head: {:?}", c);
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(
                                path,
                                func_name,
                                a,
                                locals.clone(),
                                false,
                            )?);
                        }
                        ins.push(Instruction::Ctor(c.clone(), args.len() as u8));
                    }
                    Expr::Var(_, Var::Local(v)) => {
                        // Note: v might still be a global, as it may refer to a definition in the
                        // current file (so has no namespace qualifier in the source code).
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(
                                path,
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
                                None => {
                                    let name = GlobalName::named(path, v);
                                    Instruction::PushGlobal(name.to_string())
                                }
                            });
                            ins.push(Instruction::Call);
                        }
                    }
                    Expr::Var(_, Var::Global(ns, v)) => {
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(
                                path,
                                func_name,
                                a,
                                locals.clone(),
                                false,
                            )?);
                        }

                        ins.push(Instruction::PushInt(args.len() as i64));

                        let name = self.imports.lookup((0, 0), path, ns, v).unwrap();
                        // If we're doing a tail call, use the TailCall instruction
                        if is_leaf && name.name() == func_name && name.path() == Some(path) {
                            ins.push(Instruction::TailCall);
                        } else {
                            ins.push(Instruction::PushGlobal(name.to_string()));
                            ins.push(Instruction::Call);
                        }
                    }
                    Expr::Var(_, Var::Operator(o)) => {
                        for a in args.iter().rev() {
                            ins.append(&mut self.compile_expr(
                                path,
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
                            Operator::Chars => Instruction::Chars,
                            Operator::CharAt => Instruction::CharAt,
                        });
                    }
                    h => todo!("{:?}", h),
                }
            }
            Expr::Let { bindings, body, .. } => {
                let mut locals = locals.clone();
                for b in bindings {
                    ins.append(&mut self.compile_expr(
                        path,
                        func_name,
                        &b.value,
                        locals.clone(),
                        false,
                    )?);
                    locals.push(b.name.to_string());
                }
                ins.append(&mut self.compile_expr(path, func_name, body, locals, is_leaf)?);
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
        path: &Path,
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
        let local_name = self.generate_fresh_name();
        let name = GlobalName::named(path, &local_name).to_string();
        let ins = self.compile_expr(
            path,
            &name,
            body,
            {
                let mut locals = body_locals.clone();
                locals.reverse();
                locals
            },
            true,
        )?;
        let block_id = self.program.add_block(&name, ins);
        self.functions
            .insert(name.clone(), (block_id, body_locals.to_vec()));
        Ok(name)
    }

    fn compile_operators(&mut self, path: &Path) {
        // Compile an instruction sequence for each operator so they can be used as first-class
        // functions.
        self.compile_func(
            path,
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
            path,
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
            path,
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
            path,
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
            path,
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
        self.compile_func(
            path,
            "chars",
            &Expr::Func {
                loc: (0, 0),
                args: vec![((0, 0), "s".to_string())],
                body: Box::new(Expr::App {
                    loc: (0, 0),
                    head: Box::new(Expr::Var((0, 0), Var::Operator(Operator::Chars))),
                    args: vec![Expr::Var((0, 0), Var::Local("s".to_string()))],
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
    Chars,
    CharAt,
    PushInt(i64),
    PushStr(String),
    PushChar(char),
    PushBool(bool),
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
    // Map each pattern to a relative jump
    Case(Vec<(Pattern, usize)>),
    // A relative jump forward in the instruction sequence.
    Jump(usize),
    // Shift(N) shifts the top stack element backwards, removing n elements behind it.
    // This is used when exiting the branch of a case expression to remove any locals bound in the branch.
    Shift(usize),
    Ret,
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::AddInt => write!(f, "add"),
            Instruction::SubInt => write!(f, "sub"),
            Instruction::MulInt => write!(f, "mul"),
            Instruction::LtInt => write!(f, "lt"),
            Instruction::Eq => write!(f, "eq"),
            Instruction::Chars => write!(f, "chars"),
            Instruction::CharAt => write!(f, "char_at"),
            Instruction::PushInt(i) => write!(f, "push_int {}", i),
            Instruction::PushStr(s) => write!(f, "push_str {}", s),
            Instruction::PushChar(c) => write!(f, "push_char {}", c),
            Instruction::PushBool(b) => write!(f, "push_bool {}", b),
            Instruction::PushVar(v) => write!(f, "push_var {}", v),
            Instruction::PushGlobal(g) => write!(f, "push_global {}", g),
            Instruction::PushCtor(c) => write!(f, "push_ctor {}", c),
            Instruction::MakeList(l) => write!(f, "make_list {}", l),
            Instruction::MakeTuple(t) => write!(f, "make_tuple {}", t),
            Instruction::Ctor(name, num_args) => write!(f, "ctor {:?} {}", name, num_args),
            Instruction::Call => write!(f, "call"),
            Instruction::TailCall => write!(f, "tail_call"),
            Instruction::Case(branches) => {
                write!(f, "case {{ ")?;
                for (i, (pattern, jump)) in branches.iter().enumerate() {
                    if i == branches.len() - 1 {
                        write!(f, "{} -> {} }}", pattern, jump)?;
                    } else {
                        write!(f, "{} -> {}, ", pattern, jump)?;
                    }
                }
                Ok(())
            }
            Instruction::Jump(n) => write!(f, "jmp {n}"),
            Instruction::Ret => write!(f, "ret"),
            Instruction::Shift(n) => write!(f, "shift {n}"),
        }
    }
}

#[derive(Debug)]
pub enum Error {}

#[derive(Debug, Clone, Copy)]
pub struct BlockId(pub usize);

#[derive(Debug)]
pub struct Block {
    name: String, // for debugging, not necessarily unique
    instructions: Vec<Instruction>,
}

#[derive(Debug)]
pub struct Program {
    blocks: Vec<Block>,
}

impl Program {
    pub fn new() -> Self {
        Self { blocks: vec![] }
    }

    pub fn add_block(&mut self, name: &str, instructions: Vec<Instruction>) -> BlockId {
        self.blocks.push(Block {
            name: name.to_string(),
            instructions,
        });
        BlockId(self.blocks.len() - 1)
    }

    pub fn get_block(&self, block_id: BlockId) -> &[Instruction] {
        self.blocks[block_id.0].instructions.as_slice()
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (block_id, block) in self.blocks.iter().enumerate() {
            writeln!(f, "\n{}:", block.name)?;
            for (ins_id, ins) in block.instructions.iter().enumerate() {
                writeln!(f, "{:>3} {:>3}: {}", block_id, ins_id, ins)?;
            }
        }
        Ok(())
    }
}

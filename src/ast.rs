use std::collections::VecDeque;

pub type Loc = usize;

/// A trait for types that have a source location.
pub trait HasLoc {
    fn loc(&self) -> Loc;
}

#[derive(Debug)]
pub enum Decl {
    Type { loc: Loc, name: String, constructors: Vec<TypeConstructor> },
    Func { loc: Loc, name: String, r#type: SourceType, body: Expr }
}

impl HasLoc for Decl {
    fn loc(&self) -> Loc {
        match self {
            Self::Type { loc, ..} => *loc,
            Self::Func { loc, ..} => *loc,
        }
    }
}


#[derive(Debug)]
pub struct TypeConstructor {
    pub loc: Loc,
    pub name: String,
    pub variables: Vec<String>,
    pub arguments: Vec<SourceType>
}

impl HasLoc for TypeConstructor {
    fn loc(&self) -> Loc {
        self.loc
    }
}

#[derive(Debug, Clone)]
/// A type as written in source code.
pub enum SourceType {
    Named(Loc, String),
    Func(Loc, Box<SourceType>, Box<SourceType>),
    Int(Loc),
}

impl HasLoc for SourceType {
    fn loc(&self) -> Loc {
        match self {
            Self::Named(loc, _) => *loc,
            Self::Func(loc, _, _) => *loc,
            Self::Int(loc) => *loc,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A type as used in typechecking.
pub enum Type {
    Named(String),
    Func(Box<Type>, Box<Type>),
    Int,
}

#[derive(Debug)]
pub enum Expr {
    Var(Loc, Var),
    Int(Loc, u64),
    Match { loc: Loc, target: Var, branches: Vec<MatchBranch> },
    Func { loc: Loc, args: Vec<Pattern>, body: Box<Expr> },
    App { loc: Loc, head: Box<Expr>, args: Vec<Expr> }

}

impl HasLoc for Expr {
    fn loc(&self) -> Loc {
        match self {
            Self::Var(loc, _) => *loc,
            Self::Int(loc, _) => *loc,
            Self::Match { loc, .. } => *loc,
            Self::Func { loc, .. } => *loc,
            Self::App { loc, .. } => *loc,
        }
    }
}

#[derive(Debug)]
pub struct MatchBranch {
    loc: Loc,
    pub constructor: String,
    pub args: Vec<Pattern>,
    pub rhs: Expr
}

impl HasLoc for MatchBranch {
    fn loc(&self) -> Loc {
        self.loc
    }
}

#[derive(Debug)]
pub enum Pattern {
    Var(Loc, String)
}

impl HasLoc for Pattern {
    fn loc(&self) -> Loc {
        match self {
            Self::Var(loc, _) => *loc
        }
    }
}

#[derive(Debug)]
pub enum Var {
    Local(String),
    Constructor(String),
    Operator(Operator)
}

#[derive(Debug)]
pub enum Operator {
    Add,
    Sub,
    Mul
}

impl Type {
    /// Returns a Vec of all arguments to this function type, followed by the result type.
    ///
    /// Examples:
    ///
    /// ```
    /// use tl::ast::Type;
    ///
    /// let t = Type::Func(Box::new(Type::Int), Box::new(Type::Func(Box::new(Type::Int), Box::new(Type::Int))));
    /// assert_eq!(t.func_args(), &[&Type::Int, &Type::Int, &Type::Int]);
    /// ```
    pub fn func_args(&self) -> VecDeque<&Type> {
        match self {
            Type::Func(f, x) => {
               let mut args = (*x).func_args();
               args.push_front(f);
               args
            }
            t => vec![t].into()
        }
    }

    pub fn from_func_args(args: &Vec<&Type>) -> Self {
        if args.is_empty() {
            panic!("Cannot construct type from empty args");
        }
        let mut iter = args.iter().rev();
        let mut t: Type = (*iter.next().unwrap()).clone();
        for arg in iter {
            t = Type::Func(Box::new((*arg).clone()), Box::new(t))
        }
        t
    }

    pub fn from_source_type(source_type: &SourceType) -> Self {
        match source_type {
            SourceType::Named(_, n) => Self::Named(n.to_string()),
            SourceType::Func(_, f, x) => {
                let f = Type::from_source_type(f);
                let x = Type::from_source_type(x);
                Self::Func(Box::new(f), Box::new(x))
            }
            SourceType::Int(_) => Type::Int
        }
    }
}

use std::collections::VecDeque;

#[derive(Debug)]
pub enum Decl {
    Type { name: String, constructors: Vec<TypeConstructor> },
    Func { name: String, r#type: Type, body: Expr }
}
#[derive(Debug)]
pub struct TypeConstructor {
    pub name: String,
    pub variables: Vec<String>,
    pub arguments: Vec<Type>
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Named(String),
    Func(Box<Type>, Box<Type>),
    Int,
    // TODO
}
#[derive(Debug)]
pub enum Expr {
    Var(Var),
    Int(u64),
    Match { target: Var, branches: Vec<MatchBranch> },
    Func { args: Vec<Pattern>, body: Box<Expr> },
    App { head: Box<Expr>, args: Vec<Expr> }

}
#[derive(Debug)]
pub struct MatchBranch {
    pub constructor: String,
    pub args: Vec<Pattern>,
    pub rhs: Expr
}
#[derive(Debug)]
pub enum Pattern {
    Var(String)
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
}

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
#[derive(Debug)]
pub enum Type {
    Named(String),
    Func(Box<Type>, Box<Type>)
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
    constructor: String,
    args: Vec<Pattern>,
    rhs: Expr
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

use std::collections::VecDeque;

pub type Loc = usize;

fn calculate_lines(s: &str) -> Vec<usize> {
    s.match_indices('\n').map(|(n, _)| n).collect()
}

fn string_index_to_line_col_number(
    string_index: usize,
    newline_indices: &[usize],
) -> (usize, usize) {
    // the (zero-indexed) line
    // we look for the first consecutive pair of newline indices (i, j)
    // where i <= string_index <= j
    // if no such pair exists, the location must be on the first line

    let mut line: Option<usize> = None;
    // the string index of the newline preceding this line (or 0 if it's the first line)
    let mut line_index = None;

    if let Some(i) = newline_indices.last() {
        if string_index > *i {
            // The location is on the last line
            line = Some(newline_indices.len() - 1);
            line_index = Some(*i);
        }
    }

    for (n, i_j) in newline_indices.windows(2).enumerate() {
        let i = i_j[0];
        let j = i_j[1];
        if i <= string_index && string_index <= j {
            line = Some(n);
            line_index = Some(i);
        }
    }

    let mut line = line.unwrap_or(0);
    let line_index = line_index.unwrap_or(0);

    // the column position in the line
    let col = if line == 0 {
        string_index - line_index + 1
    } else {
        string_index - line_index
    };

    if line == 0 {
        line = 1;
    } else {
        line += 2;
    }

    (line, col)
}

// Print the line before the error location,
// then the line with the error.
// Then print a caret (^) indicating the error
// e.g.
//
// f : A -> A {
//   x => x
//     ^
// expected '-'
//
pub fn print_error<E: std::fmt::Display + HasLoc, W: std::io::Write>(writer: &mut W, orig: &str, error: E) {
    let loc = error.loc();
    let newlines = calculate_lines(orig);
    let (line, col) = string_index_to_line_col_number(loc, &newlines);
    let mut source_lines = orig.split('\n');

    // Print the previous line, if it exists
    if line > 1 {
        writeln!(writer, "{:>4}: {}", line - 1, source_lines.nth(line - 2).unwrap()).unwrap();
        writeln!(writer, "{:>4}: {}", line, source_lines.next().unwrap()).unwrap();
    } else {
        writeln!(writer, "{:>4}: {}", line, source_lines.nth(line - 1).unwrap()).unwrap();
    }
    writeln!(writer, "     {}^", " ".repeat(col)).unwrap();
    writeln!(writer, "     {} {}", " ".repeat(col), error.to_string()).unwrap();
}

/// A trait for types that have a source location.
pub trait HasLoc {
    fn loc(&self) -> Loc;
}

#[derive(Debug)]
pub enum Decl {
    Type {
        loc: Loc,
        name: String,
        constructors: Vec<TypeConstructor>,
    },
    Func {
        loc: Loc,
        name: String,
        r#type: SourceType,
        body: Expr,
    },
}

impl HasLoc for Decl {
    fn loc(&self) -> Loc {
        match self {
            Self::Type { loc, .. } => *loc,
            Self::Func { loc, .. } => *loc,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeConstructor {
    pub loc: Loc,
    pub name: String,
    pub variables: Vec<String>,
    pub arguments: Vec<SourceType>,
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
    App {
        loc: Loc,
        head: Box<SourceType>,
        args: Vec<SourceType>,
    },
}

impl HasLoc for SourceType {
    fn loc(&self) -> Loc {
        match self {
            Self::Named(loc, _) => *loc,
            Self::Func(loc, _, _) => *loc,
            Self::Int(loc) => *loc,
            Self::App { loc, ..} => *loc,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A type as used in typechecking.
pub enum Type {
    Named(String),
    Func(Box<Type>, Box<Type>),
    Int,
    App { head: Box<Type>, args: Vec<Type> },
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.fmt_with_context(f, TypeFormatContext::Neutral)
    }
}

enum TypeFormatContext {
    Neutral,
    FuncLeft,
    AppRight,
    AppLeft,
}

impl Type {
    fn fmt_with_context(&self, f: &mut std::fmt::Formatter<'_>, context: TypeFormatContext) -> Result<(), std::fmt::Error> {
        match self {
            Type::Named(n) => write!(f, "{}", n),
            Type::Func(func, arg) => match context {
                TypeFormatContext::Neutral => {
                    (*func).fmt_with_context(f, TypeFormatContext::FuncLeft)?;
                    write!(f, " -> ")?;
                    (*arg).fmt_with_context(f, TypeFormatContext::Neutral)
                }
                TypeFormatContext::FuncLeft | TypeFormatContext::AppRight | TypeFormatContext::AppLeft => {
                    write!(f, "(")?;
                    self.fmt_with_context(f, TypeFormatContext::Neutral)?;
                    write!(f, ")")
                }
            }
            Type::Int => write!(f, "Int"),
            Type::App { head, args } => match context {
                TypeFormatContext::Neutral | TypeFormatContext::AppLeft => {
                    (*head).fmt_with_context(f, TypeFormatContext::AppLeft)?;
                    write!(f, " ")?;
                    for arg in args {
                        arg.fmt_with_context(f, TypeFormatContext::AppRight)?;
                    }
                    Ok(())
                },
                TypeFormatContext::FuncLeft | TypeFormatContext::AppRight => {
                    write!(f, "(")?;
                    self.fmt_with_context(f, TypeFormatContext::Neutral)?;
                    write!(f, ")")
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum Expr {
    Var(Loc, Var),
    Int(Loc, u64),
    Match {
        loc: Loc,
        target: Var,
        branches: Vec<MatchBranch>,
    },
    Func {
        loc: Loc,
        args: Vec<Pattern>,
        body: Box<Expr>,
    },
    App {
        loc: Loc,
        head: Box<Expr>,
        args: Vec<Expr>,
    },
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
    pub loc: Loc,
    pub constructor: String,
    pub args: Vec<Pattern>,
    pub rhs: Expr,
}

impl HasLoc for MatchBranch {
    fn loc(&self) -> Loc {
        self.loc
    }
}

#[derive(Debug)]
pub enum Pattern {
    Var(Loc, String),
}

impl std::fmt::Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Pattern::Var(_, n) => write!(f, "{}", n)
        }
    }
}

impl HasLoc for Pattern {
    fn loc(&self) -> Loc {
        match self {
            Self::Var(loc, _) => *loc,
        }
    }
}

#[derive(Debug)]
pub enum Var {
    Local(String),
    Constructor(String),
    Operator(Operator),
}

#[derive(Debug)]
pub enum Operator {
    Add,
    Sub,
    Mul,
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
            t => vec![t].into(),
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
            SourceType::Int(_) => Type::Int,
            SourceType::App { head, args, .. } => {
                let head = Type::from_source_type(head);
                let args = args.iter().map(|arg| Type::from_source_type(arg)).collect();
                Self::App { head: Box::new(head), args }
            }
        }
    }
}

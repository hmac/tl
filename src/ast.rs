use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Display,
    path::{Path, PathBuf},
};

/// (start, end) index pair into the source string
pub type Loc = (usize, usize);

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
            line = Some(newline_indices.len());
            line_index = Some(*i);
        }
    }

    for (n, i_j) in newline_indices.windows(2).enumerate() {
        let i = i_j[0];
        let j = i_j[1];
        if i <= string_index && string_index <= j {
            line = Some(n + 1);
            line_index = Some(i);
        }
    }

    let line = line.unwrap_or(0);
    let line_index = line_index.unwrap_or(0);

    // the column position in the line
    let col = if line == 0 {
        string_index - line_index + 1
    } else {
        string_index - line_index
    };

    (line + 1, col)
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
pub fn print_error<E: Display + HasLoc, W: std::io::Write>(writer: &mut W, orig: &str, error: E) {
    let (start, end) = error.loc();
    let newlines = calculate_lines(orig);
    let (start_line, start_col) = string_index_to_line_col_number(start, &newlines);
    let (end_line, mut end_col) = string_index_to_line_col_number(end, &newlines);
    let mut source_lines = orig.split('\n');

    // We don't yet know how to print errors that span multiple lines.
    // If the error crosses a newline, we'll just set (end_line, end_col)
    // to (start_line, <max col in start_line>).
    if end_line > start_line {
        // end_line = start_line;
        end_col = start_col; // TODO
    }

    // Print the previous line, if it exists
    // We assume that start_line == end_line for now
    if start_line > 1 {
        writeln!(
            writer,
            "{:>4}: {}",
            start_line - 1,
            source_lines.nth(start_line - 2).unwrap()
        )
        .unwrap();
        writeln!(
            writer,
            "{:>4}: {}",
            start_line,
            source_lines.next().unwrap()
        )
        .unwrap();
    } else {
        writeln!(
            writer,
            "{:>4}: {}",
            start_line,
            source_lines.nth(start_line - 1).unwrap()
        )
        .unwrap();
    }
    writeln!(
        writer,
        "     {}{}",
        " ".repeat(start_col),
        "^".repeat(1.max(end_col - start_col))
    )
    .unwrap();
    writeln!(
        writer,
        "     {} {}",
        " ".repeat(start_col),
        error.to_string()
    )
    .unwrap();
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
        params: Vec<String>,
        constructors: Vec<TypeConstructor>,
    },
    Func {
        loc: Loc,
        name: String,
        r#type: SourceType,
        body: Expr,
    },
    Import {
        loc: Loc,
        name: String,
        name_loc: Loc,
        path: PathBuf,
        path_loc: Loc,
    },
    Test {
        loc: Loc,
        name: String,
        body: Expr,
    },
}

impl HasLoc for Decl {
    fn loc(&self) -> Loc {
        match self {
            Self::Type { loc, .. } => *loc,
            Self::Func { loc, .. } => *loc,
            Self::Import { loc, .. } => *loc,
            Self::Test { loc, .. } => *loc,
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
    Named(Loc, Option<Namespace>, String),
    Func(Loc, Box<SourceType>, Box<SourceType>),
    Int(Loc),
    Bool(Loc),
    Str(Loc),
    Char(Loc),
    Tuple {
        loc: Loc,
        elems: Vec<SourceType>,
    },
    App {
        loc: Loc,
        head: Box<SourceType>,
        args: Vec<SourceType>,
    },
    Var(Loc, String),
}

impl HasLoc for SourceType {
    fn loc(&self) -> Loc {
        match self {
            Self::Named(loc, _, _) => *loc,
            Self::Func(loc, _, _) => *loc,
            Self::Int(loc) => *loc,
            Self::Bool(loc) => *loc,
            Self::Str(loc) => *loc,
            Self::Char(loc) => *loc,
            Self::App { loc, .. } => *loc,
            Self::Var(loc, _) => *loc,
            Self::Tuple { loc, .. } => *loc,
        }
    }
}

/// A name qualified by the path to the file that defines it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GlobalName {
    Builtin(String),
    Named(PathBuf, String),
}

impl GlobalName {
    pub fn builtin(name: &str) -> Self {
        Self::Builtin(name.to_string())
    }

    pub fn named(path: &Path, name: &str) -> Self {
        Self::Named(path.to_path_buf(), name.to_string())
    }

    pub fn name(&self) -> &str {
        match self {
            Self::Builtin(s) => s,
            Self::Named(_, s) => s,
        }
    }

    pub fn path(&self) -> Option<&Path> {
        match self {
            Self::Builtin(_) => None,
            Self::Named(p, _) => Some(p),
        }
    }

    pub fn display_name_relative_to_path(&self, path: &Path) -> String {
        match self {
            Self::Builtin(s) => s.to_string(),
            Self::Named(p, s) if p == path => s.to_string(),
            Self::Named(p, s) => format!("{}:{s}", p.display()),
        }
    }
}

impl std::fmt::Display for GlobalName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Builtin(s) => write!(f, "{s}"),
            Self::Named(path, s) => write!(f, "{}:{s}", path.display()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A type as used in typechecking.
pub enum Type {
    Named(GlobalName),
    Func(Box<Type>, Box<Type>),
    Int,
    Str,
    Char,
    Bool,
    Tuple(Vec<Type>),
    App { head: Box<Type>, args: Vec<Type> },
    Var(String),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.with_path(None).fmt(f)
    }
}

impl Type {
    pub fn vars(&self) -> Vec<String> {
        match self {
            Type::Named(_) | Type::Int | Type::Bool | Type::Str | Type::Char => vec![],
            Type::Func(f, x) => {
                let mut vars = f.vars();
                vars.append(&mut x.vars());
                vars
            }
            Type::App { head, args } => {
                let mut vars = head.vars();
                for arg in args {
                    vars.append(&mut arg.vars());
                }
                vars
            }
            Type::Tuple(elems) => elems.iter().flat_map(Self::vars).collect(),
            Type::Var(v) => vec![v.to_string()],
        }
    }

    pub fn with_path<'a>(&'a self, path: Option<&'a Path>) -> TypeWithContext<'a> {
        TypeWithContext {
            r#type: self,
            path,
            ctx: TypeFormatContext::Neutral,
        }
    }
}

pub struct TypeWithContext<'a> {
    r#type: &'a Type,
    path: Option<&'a Path>,
    ctx: TypeFormatContext,
}

impl<'a> TypeWithContext<'a> {
    pub fn with_context(&self, ctx: TypeFormatContext) -> TypeWithContext<'a> {
        TypeWithContext {
            r#type: self.r#type,
            path: self.path,
            ctx,
        }
    }
}

impl<'a> std::fmt::Display for TypeWithContext<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.r#type {
            Type::Named(name) => match self.path {
                Some(path) => write!(f, "{}", name.display_name_relative_to_path(path)),
                None => write!(f, "{name}"),
            },
            Type::Var(v) => write!(f, "{}", v),
            Type::Func(func, arg) => match self.ctx {
                TypeFormatContext::Neutral => {
                    func.with_path(self.path)
                        .with_context(TypeFormatContext::FuncLeft)
                        .fmt(f)?;
                    write!(f, " -> ")?;
                    arg.with_path(self.path).fmt(f)
                }
                TypeFormatContext::FuncLeft
                | TypeFormatContext::AppRight
                | TypeFormatContext::AppLeft => {
                    write!(f, "(")?;
                    self.with_context(TypeFormatContext::Neutral).fmt(f)?;
                    write!(f, ")")
                }
            },
            Type::Int => write!(f, "Int"),
            Type::Str => write!(f, "String"),
            Type::Bool => write!(f, "Bool"),
            Type::Char => write!(f, "Char"),
            Type::Tuple(elems) => {
                if elems.is_empty() {
                    write!(f, "(,)")
                } else {
                    let n = elems.len();
                    for (i, e) in elems.iter().enumerate() {
                        if i == 0 {
                            write!(f, "({e},")?;
                        } else if i > 0 && i == n - 1 {
                            write!(f, " {}", e)?;
                        } else {
                            write!(f, " {},", e)?;
                        }
                    }
                    write!(f, ")")
                }
            }
            Type::App { head, args } => match self.ctx {
                TypeFormatContext::Neutral | TypeFormatContext::AppLeft => {
                    head.with_path(self.path)
                        .with_context(TypeFormatContext::AppLeft)
                        .fmt(f)?;
                    for arg in args {
                        write!(f, " ")?;
                        arg.with_path(self.path)
                            .with_context(TypeFormatContext::AppRight)
                            .fmt(f)?;
                    }
                    Ok(())
                }
                TypeFormatContext::FuncLeft | TypeFormatContext::AppRight => {
                    write!(f, "(")?;
                    self.with_context(TypeFormatContext::Neutral).fmt(f)?;
                    write!(f, ")")
                }
            },
        }
    }
}

pub enum TypeFormatContext {
    Neutral,
    FuncLeft,
    AppRight,
    AppLeft,
}

impl Type {
    pub fn rename_vars(&mut self, substitution: &HashMap<String, String>) {
        match self {
            Type::Named(_) | Type::Int | Type::Bool | Type::Str | Type::Char => {}
            Type::Func(f, x) => {
                f.rename_vars(substitution);
                x.rename_vars(substitution);
            }
            Type::App { head, args } => {
                head.rename_vars(substitution);
                for arg in args {
                    arg.rename_vars(substitution);
                }
            }
            Type::Var(v) => {
                if let Some(new_var) = substitution.get(v) {
                    *v = new_var.clone();
                }
            }
            Type::Tuple(elems) => {
                for e in elems.iter_mut() {
                    e.rename_vars(substitution);
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Var(Loc, Var),
    Int(Loc, i64),
    Str(Loc, String),
    Char(Loc, char),
    Tuple {
        loc: Loc,
        elems: Vec<Expr>,
    },
    List {
        loc: Loc,
        elems: Vec<Expr>,
        tail: Option<Box<Expr>>,
    },
    Case {
        loc: Loc,
        target: Box<Expr>,
        branches: Vec<CaseBranch>,
    },
    Func {
        loc: Loc,
        args: Vec<(Loc, String)>,
        body: Box<Expr>,
    },
    App {
        loc: Loc,
        head: Box<Expr>,
        args: Vec<Expr>,
    },
    Let {
        loc: Loc,
        bindings: Vec<LetBinding>,
        body: Box<Expr>,
    },
}

impl Expr {
    pub fn free_variables(&self) -> HashSet<&String> {
        match self {
            Expr::Var(_, Var::Local(v)) => [v].into(),
            Expr::Var(_, _) => HashSet::new(),
            Expr::Int(_, _) => HashSet::new(),
            Expr::Str(_, _) => HashSet::new(),
            Expr::Char(_, _) => HashSet::new(),
            Expr::Tuple { elems, .. } => elems.iter().flat_map(Self::free_variables).collect(),
            Expr::List { elems, tail, .. } => {
                let mut vars: HashSet<&String> =
                    elems.iter().flat_map(Self::free_variables).collect();
                if let Some(tail) = tail {
                    vars = vars.union(&tail.free_variables()).map(|x| *x).collect();
                }
                vars
            }
            Expr::Case { branches, .. } => {
                let mut vars = HashSet::new();
                for b in branches {
                    for v in b.rhs.free_variables().difference(&b.pattern.vars()) {
                        vars.insert(*v);
                    }
                }
                vars
            }
            Expr::Func { args, body, .. } => {
                let mut vars = HashSet::new();
                for v in body
                    .free_variables()
                    .difference(&args.iter().map(|a| &a.1).collect())
                {
                    vars.insert(*v);
                }
                vars
            }
            Expr::App { head, args, .. } => args
                .iter()
                .flat_map(Self::free_variables)
                .chain(head.free_variables().into_iter())
                .collect(),
            Expr::Let { bindings, body, .. } => {
                let mut free_vars = HashSet::new();
                let mut bound_vars = HashSet::new();
                for b in bindings {
                    free_vars = free_vars
                        .union(
                            &b.value
                                .free_variables()
                                .difference(&bound_vars)
                                .map(|v| *v)
                                .collect(),
                        )
                        .map(|v| *v)
                        .collect();
                    bound_vars.insert(&b.name);
                }
                free_vars = free_vars
                    .union(
                        &body
                            .free_variables()
                            .difference(&bound_vars)
                            .map(|v| *v)
                            .collect(),
                    )
                    .map(|v| *v)
                    .collect();
                free_vars
            }
        }
    }
}

impl HasLoc for Expr {
    fn loc(&self) -> Loc {
        match self {
            Self::Var(loc, _) => *loc,
            Self::Int(loc, _) => *loc,
            Self::Str(loc, _) => *loc,
            Self::Char(loc, _) => *loc,
            Self::Tuple { loc, .. } => *loc,
            Self::List { loc, .. } => *loc,
            Self::Case { loc, .. } => *loc,
            Self::Func { loc, .. } => *loc,
            Self::App { loc, .. } => *loc,
            Self::Let { loc, .. } => *loc,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LetBinding {
    pub loc: Loc,
    pub name: String,
    pub r#type: Option<SourceType>,
    pub value: Expr,
}

#[derive(Debug, Clone)]
pub struct CaseBranch {
    pub loc: Loc,
    pub pattern: Pattern,
    pub rhs: Expr,
}

impl HasLoc for CaseBranch {
    fn loc(&self) -> Loc {
        self.loc
    }
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Constructor {
        loc: Loc,
        namespace: Option<Namespace>,
        name: String,
        args: Vec<Pattern>,
    },
    Var {
        loc: Loc,
        name: String,
    },
    Int {
        loc: Loc,
        value: i64,
    },
    Wildcard {
        loc: Loc,
    },
    ListNil {
        loc: Loc,
    },
    // [x]
    // [x, 1]
    // [x, 1, [y]]
    // [x, 1, [y], ..z]
    ListCons {
        loc: Loc,
        elems: Vec<Pattern>,
        tail: Option<Box<Pattern>>,
    },
    Tuple {
        loc: Loc,
        elems: Vec<Pattern>,
    },
}

impl Pattern {
    pub fn vars(&self) -> HashSet<&String> {
        match self {
            Pattern::Constructor { args, .. } => args.iter().flat_map(Self::vars).collect(),
            Pattern::Var { name, .. } => [name].into(),
            Pattern::Int { .. } => HashSet::new(),
            Pattern::Wildcard { .. } => HashSet::new(),
            Pattern::ListNil { .. } => HashSet::new(),
            Pattern::ListCons { elems, tail, .. } => {
                let mut vars: HashSet<&String> = elems.iter().flat_map(Self::vars).collect();
                if let Some(tail) = tail {
                    vars = vars.union(&tail.vars()).map(|x| *x).collect();
                }
                vars
            }
            Pattern::Tuple { elems, .. } => elems.iter().flat_map(Self::vars).collect(),
        }
    }

    /// Like `vars` but returns a `Vec<String>` which lists the variables in the order they are
    /// bound. We define this order as left-to-right and depth-first, so e.g.
    /// `Cons (Some (Pair x y)) (Cons r z)` has the result `[x, y, r, z]`
    pub fn ordered_vars(&self) -> Vec<String> {
        match self {
            Pattern::Constructor { args, .. } => {
                let mut vars = vec![];
                for a in args {
                    vars.append(&mut a.ordered_vars());
                }
                vars
            }
            Pattern::Var { name, .. } => vec![name.to_string()],
            Pattern::Int { .. } => vec![],
            Pattern::Wildcard { .. } => vec![],
            Pattern::ListNil { .. } => vec![],
            Pattern::ListCons { elems, tail, .. } => {
                let mut vars: Vec<String> = elems.iter().flat_map(Self::ordered_vars).collect();
                if let Some(tail) = tail {
                    vars.append(&mut tail.ordered_vars());
                }
                vars
            }
            Pattern::Tuple { elems, .. } => elems.iter().flat_map(Self::ordered_vars).collect(),
        }
    }
}

impl std::fmt::Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Pattern::Constructor { name, args, .. } => {
                write!(f, "{}", name)?;
                // TODO: nested patterns need parens
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                Ok(())
            }
            Pattern::Int { value, .. } => write!(f, "{}", value),
            Pattern::Var { name, .. } => write!(f, "{}", name),
            Pattern::Wildcard { .. } => write!(f, "_"),
            Pattern::ListNil { .. } => write!(f, "[]"),
            Pattern::ListCons { elems, tail, .. } => {
                write!(f, "[")?;
                let mut elems_iter = elems.iter();
                if let Some(e) = elems_iter.next() {
                    write!(f, "{}", e)?;
                }
                for e in elems_iter {
                    write!(f, ", {}", e)?;
                }
                if let Some(tail) = tail {
                    write!(f, "..{}]", tail)?;
                } else {
                    write!(f, "]")?;
                }
                Ok(())
            }
            Pattern::Tuple { elems, .. } => {
                write!(f, "(")?;
                let mut elems_iter = elems.iter();
                if let Some(e) = elems_iter.next() {
                    write!(f, "{}", e)?;
                }
                for e in elems_iter {
                    write!(f, ", {}", e)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl HasLoc for Pattern {
    fn loc(&self) -> Loc {
        match self {
            Self::Var { loc, .. } => *loc,
            Self::Int { loc, .. } => *loc,
            Self::Constructor { loc, .. } => *loc,
            Self::Wildcard { loc, .. } => *loc,
            Self::ListNil { loc } => *loc,
            Self::ListCons { loc, .. } => *loc,
            Self::Tuple { loc, .. } => *loc,
        }
    }
}

/// The name of an import, e.g. `myName` in
///   import ./path/to/file.tl as myName
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Namespace(String);

impl Namespace {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<String> for Namespace {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl std::fmt::Display for Namespace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub enum Var {
    Local(String),
    Global(Option<Namespace>, String),
    Constructor(Option<Namespace>, String),
    Operator(Operator),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operator {
    Add,
    Sub,
    Mul,
    Eq,
    Lt,
    Chars,
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
}

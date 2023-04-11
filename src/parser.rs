use crate::ast::{Expr, Type, Decl, TypeConstructor, Var, Pattern, Operator};
use std::collections::VecDeque;

type Loc = usize;

#[derive(Debug)]
pub enum Error {
    ExpectedLowerIdent(Loc),
    ExpectedUpperIdent(Loc),
    ExpectedNamedType(Loc),
    ExpectedPattern(Loc),
    ExpectedExpr(Loc),
    ExpectedStr(&'static str, Loc),
    ExpectedOperator(Loc),
    ExpectedInteger(Loc),
    UnexpectedEof(Loc),
}

impl Error {
    pub fn loc(&self) -> Loc {
        match self {
            Error::ExpectedLowerIdent(loc) => *loc,
            Error::ExpectedUpperIdent(loc) => *loc,
            Error::ExpectedNamedType(loc) => *loc,
            Error::ExpectedExpr(loc) => *loc,
            Error::ExpectedPattern(loc) => *loc,
            Error::ExpectedStr(_, loc) => *loc,
            Error::ExpectedOperator(loc) => *loc,
            Error::ExpectedInteger(loc) => *loc,
            Error::UnexpectedEof(loc) => *loc,
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Error::ExpectedLowerIdent(_) => {write!(f, "expected lowercase word") },
            Error::ExpectedUpperIdent(_) => {write!(f, "expected uppercase word") },
            Error::ExpectedNamedType(_) => {write!(f, "expected a named type") },
            Error::ExpectedExpr(_) => {write!(f, "expected an expression") },
            Error::ExpectedPattern(_) => {write!(f, "expected a pattern") },
            Error::ExpectedStr(s, _) => {write!(f, "expected '{}'", s)},
            Error::ExpectedOperator(_) => {write!(f, "expected '+' or '-' or '*'")},
            Error::ExpectedInteger(_) => {write!(f, "expected an integer")},
            Error::UnexpectedEof(_) => {write!(f, "unexpected EOF")},
        }
    }
}

fn calculate_lines(s: &str) -> Vec<usize> {
    s.match_indices('\n').map(|(n,_)| n).collect()
}

fn string_index_to_line_col_number(string_index: usize, newline_indices: &[usize]) -> (usize, usize) {
    // the (zero-indexed) line
    // we look for the first consecutive pair of newline indices (i, j)
    // where i <= string_index <= j
    // if no such pair exists, the location must be on the first line
    let line = {
        newline_indices.windows(2).position(|i_j| {
            let i = i_j[0];
            let j = i_j[1];
            i <= string_index && string_index <= j
        }).unwrap_or(0)
        // let i = newline_indices.iter().rev().position(|l| *l < string_index).unwrap_or(0);
        // newline_indices.len() - i - 1
    };
    // the string index of the newline preceding this line (or 0 if it's the first line)
    let line_index = newline_indices.get(line).unwrap_or(&0);
    // the column position in the line
    let col = string_index - line_index;
    (line + 2, col + 1)
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
pub fn print_error(orig: &str, error: Error) {
    let loc = error.loc();
    let (line, col) = string_index_to_line_col_number(loc, &calculate_lines(orig));
    let mut source_lines = orig.split('\n');
    // Print the previous line, if it exists
    match source_lines.nth(line - 2) {
        Some(l) => {
            println!("{}: {}", line - 1, l);
            println!("{}: {}", line, source_lines.next().unwrap());
        }
        None => {
            println!("{}: {}", line, source_lines.nth(line - 1).unwrap());
        }
    }
    println!("{}^", " ".repeat(col));
    println!("{} {}", " ".repeat(col), error.to_string());

}

pub struct Parser {
    orig: String,
    loc: usize
}

impl Parser {
    pub fn new(orig: String) -> Self {
        Self { orig, loc: 0 }
    }

    pub fn into_input(self) -> String {
        self.orig
    }

    fn input(&self) -> &str {
        &self.orig[self.loc..]
    }

    fn try_eat(&mut self, s: &'static str) -> Option<()> {
        if self.input().starts_with(&s) {
            self.loc += s.len();
            Some(())
        } else {
            None
        }
    }

    fn eat(&mut self, s: &'static str) -> Result<(), Error> {
        match self.try_eat(s) {
            Some(_) => Ok(()),
            None => Err(Error::ExpectedStr(s, self.loc)),
        }
    }

    fn eat_char(&mut self) -> Result<char, Error> {
        match self.input().chars().next() {
            Some(c) => {
                self.loc += 1;
                Ok(c)
            }, 
            None => Err(Error::UnexpectedEof(self.loc))
        }
    }

    fn trim(&mut self) {
        let mut len = 0;
        while self.input()[len..].starts_with(whitespace_char) {
            len += 1;
        }

        // Skip line comments
        loop {
            if self.input()[len..].starts_with("//") {
                while !self.input()[len..].starts_with('\n') {
                    len += 1;
                }
                len += 1;
            } else {
                break;
            }
        }

        self.loc += len;
    }

    pub fn parse(&mut self) -> Result<Vec<Decl>, Error> {
        let mut decls = vec![];
        while !self.input().is_empty() {
            self.trim();
            let decl = self.parse_decl()?;
            decls.push(decl);
        }
        Ok(decls)
    }

    fn parse_decl(&mut self) -> Result<Decl, Error> {
        match self.try_eat("type") {
            Some(_) => {
                self.trim();
                let name = self.parse_upper_ident()?;
                self.trim();
                self.eat("{")?;
                let mut constructors = vec![];
                loop {
                    self.trim();
                    match self.try_eat("}") {
                        Some(r) => {
                            break;
                        }
                        None => {
                            let ctor = self.parse_type_constructor()?;
                            constructors.push(ctor);
                            self.trim();
                            self.try_eat(","); // optional
                        }
                    }
                }
                Ok(Decl::Type{name, constructors })
            },
            None => {
                let name = self.parse_lower_ident()?;
                self.trim();
                self.eat(":")?;
                self.trim();
                let r#type = self.parse_type()?;
                self.trim();
                self.eat("{")?;
                self.trim();
                let body = self.parse_expr()?;
                self.eat("}")?;
                self.trim();
                Ok(Decl::Func{name, r#type, body})
            }
        }
    }

    fn parse_type(&mut self) -> Result<Type, Error> {
        // Parse a sequence of "type components", which are things that can make up a type.
        // We then construct the actual type from this sequence.
        // This allows us to deal with the '->' operator.
        let mut components = vec![];
        loop {
            match self.try_parse_type_component() {
                Some(c) => {components.push(c); },
                None => {break; }
            }
            self.trim();
        }

        // Now convert the list of components into a type.
        self.make_type_from_components(components)
    }

    fn make_type_from_components(&self, mut components: Vec<(Loc, TypeComponent)>) -> Result<Type, Error> {
        if components.len() == 1 {
            return match components.pop().unwrap() {
                (_, TypeComponent::Named(c)) => Ok(Type::Named(c)),
                (loc, TypeComponent::Arrow) => Err(Error::ExpectedNamedType(loc))
            }
        }

        let ty = match components.pop().unwrap() {
            (_, TypeComponent::Named(c)) => Type::Named(c),
            (loc, TypeComponent::Arrow) => { return Err(Error::ExpectedNamedType(loc)) }
        };

        match components.pop() {
            Some((loc, c)) => {
                match c {
                    TypeComponent::Arrow => {
                        let rest = self.make_type_from_components(components)?;
                        Ok(Type::Func(Box::new(ty), Box::new(rest)))
                    }
                    TypeComponent::Named(n) => {
                        unimplemented!()
                    }
                }

            },
            None => Ok(ty)
        }
    }

    fn try_parse_type_component(&mut self) -> Option<(Loc, TypeComponent)> {
        let loc = self.loc;
        match self.try_eat("->") {
            Some(_) => Some((loc, TypeComponent::Arrow)),
            None => {
                let name = self.parse_upper_ident();
                match name {
                    Err(_) => None,
                    Ok(n) => Some((loc, TypeComponent::Named(n)))
                }
            }
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, Error> {
        if self.input().starts_with(numeric_char) {
            return self.parse_int();
        }
        if self.input().starts_with("match") {
            return self.parse_match();
        }

        // Otherwise, it's a function application or a function
        // f x y
        // x y z -> e

        // Parse a sequence of expressions until we find a non-expression such as '{' or '}',
        // or an arrow '->'.
        //
        // If we find an arrow, assume we're looking at a function.
        // Re-parse the sequence as patterns, and then continue parsing the
        // function body.
        //
        // Otherwise, assume we're looking at a function application.
        let mut exprs: VecDeque<(Loc, Expr)> = VecDeque::new();
        loop {
            let loc = self.loc;
            match dbg!(self.parse_expr_nested()) {
                Err(_) => {
                    // We've found a non-expression, so stop parsing.
                    // Check if it's an arrow.
                    if self.input().starts_with("->") {
                        // Check that the preceding expressions are patterns
                        let mut args = vec![];
                        for (loc, e) in exprs {
                            match e {
                                Expr::Var(Var::Local(n)) => {
                                    args.push(Pattern::Var(n));
                                },
                                _ => {return Err(Error::ExpectedPattern(loc));}
                            }
                        }

                        // Consume the arrow
                        self.eat("->")?;
                        self.trim();

                        // Parse the function body
                        let body = self.parse_expr()?;
                        self.trim();

                        return Ok(Expr::Func { args, body: Box::new(body) })
                    }

                    // It's not an arrow, so the preceding expressions form an application
                    // Construct the application
                    match exprs.pop_front() {
                        None => { return Err(Error::ExpectedExpr(self.loc)); }
                        Some((_, f)) => {
                            let args = exprs.into_iter().map(|(_, e)| e).collect();
                            return Ok(Expr::App{head: Box::new(f), args});
                        }
                    }

                },
                Ok(expr) => {
                    exprs.push_back((loc, expr));
                    self.trim();
                }
            }
        }
    }

    /// Like `parse_expr` but functions and applications must be wrapped in parens.
    fn parse_expr_nested(&mut self) -> Result<Expr, Error> {
        if self.input().starts_with(numeric_char) {
            return self.parse_int();
        }
        if self.input().starts_with("match") {
            return self.parse_match();
        }
        if self.input().starts_with("(") {
            self.eat("(")?;
            let e = self.parse_expr()?;
            self.eat(")")?;
            self.trim();
            return Ok(e);
        }
        if self.input().starts_with(lower_ident_char) {
            let n = self.parse_lower_ident()?;
            return Ok(Expr::Var(Var::Local(n)));
        }
        if self.input().starts_with(upper_ident_char) {
            let n = self.parse_upper_ident()?;
            return Ok(Expr::Var(Var::Constructor(n)));
        }
        if self.input().starts_with(operator_char) {
            // To ensure we don't parse x -> y as x - <parse error>
            if !self.input().starts_with("->") {
                return self.parse_operator();
            }
        }
        Err(Error::ExpectedExpr(self.loc))
    }

    fn parse_match(&mut self) -> Result<Expr, Error> {
        unimplemented!()
    }

    fn parse_int(&mut self) -> Result<Expr, Error> {
        let mut len = 0;
        while self.input()[len..].starts_with(char::is_numeric) {
            len += 1;
        }

        let (s, _) = self.input().split_at(len);
        match s.parse() {
            Ok(n) => {
                self.loc += len;
                Ok(Expr::Int(n))
            },
            Err(_) => Err(Error::ExpectedInteger(self.loc)),
        }
    }

    fn parse_operator(&mut self) -> Result<Expr, Error> {
        let op = self.eat_char()?;
        let op = match op {
            '+' => Operator::Add,
            '-' => Operator::Sub,
            '*' => Operator::Mul,
            _ => { return Err(Error::ExpectedOperator(self.loc - 1)); }
        };
        Ok(Expr::Var(Var::Operator(op)))
    }

    fn parse_type_constructor(&mut self) -> Result<TypeConstructor, Error> {
        let name = self.parse_upper_ident()?;
        Ok(TypeConstructor { name, variables: vec![], arguments: vec![] })
    }

    fn parse_upper_ident(&mut self) -> Result<String, Error> {
        if !self.input().starts_with(upper_ident_char) {
            return Err(Error::ExpectedUpperIdent(self.loc))
        }

        let mut len = 1;

        while self.input()[len..].starts_with(alpha_or_underscore_char) {
            len += 1;
        }

        let (m, _) = self.input().split_at(len);
        let m = m.to_string();
        self.loc += len;
        Ok(m)
    }

    fn parse_lower_ident(&mut self) -> Result<String, Error> {
        if !self.input().starts_with(lower_ident_char) {
            return Err(Error::ExpectedLowerIdent(self.loc))
        }

        let mut len = 1;

        while self.input()[len..].starts_with(alpha_or_underscore_char) {
            len += 1;
        }

        let (m, _) = self.input().split_at(len);
        let m = m.to_string();
        self.loc += len;
        Ok(m)
    }

}

fn lower_ident_char(c: char) -> bool {
    c == '_' || (c >= 'a' && c <= 'z')
}

fn upper_ident_char(c: char) -> bool {
    c == '_' || (c >= 'A' && c <= 'Z')
}

fn alpha_or_underscore_char(c: char) -> bool {
    c == '_' || (c >= 'A' && c <= 'z')
}

fn whitespace_char(c: char) -> bool {
    c == ' ' || c == '\n'
}

fn numeric_char(c: char) -> bool {
    c >= '0' && c <= '9'
}

fn operator_char(c: char) -> bool {
    c == '+' || c == '-'  || c == '*'
}


#[derive(Debug)]
enum TypeComponent {
    Arrow,
    Named(String)
}

#[derive(Debug)]
enum ExprComponent {
    Var(String),
    Constructor(String),
    Int(u64),
}

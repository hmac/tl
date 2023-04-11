use crate::ast::{Expr, Type, Decl, TypeConstructor, Var, Pattern};

type Loc = usize;

#[derive(Debug)]
pub enum Error {
    ExpectedLowerIdent(Loc),
    ExpectedUpperIdent(Loc),
    ExpectedNamedType(Loc),
    ExpectedPattern(Loc),
    ExpectedExpr(Loc),
    ExpectedStr(&'static str, Loc)
}

impl Error {
    pub fn loc(&self) -> Loc {
        match self {
            Error::ExpectedLowerIdent(loc) => *loc,
            Error::ExpectedUpperIdent(loc) => *loc,
            Error::ExpectedNamedType(loc) => *loc,
            Error::ExpectedExpr(loc) => *loc,
            Error::ExpectedPattern(loc) => *loc,
            Error::ExpectedStr(_, loc) => *loc
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
        }
    }
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
    // Find the nearest newline before the error loc, if one exists
    let (str_before_err, str_after_err) = orig.split_at(loc);
    match str_before_err.rfind('\n') {
        Some(newline1) => {
            // there is at least one newline before error.
            // now we try to find another.
            let str_before_newline = &str_before_err[0..newline1];
            match str_before_newline.rfind('\n') {
                Some(newline2) => {
                    // Now find the newline after the error.
                    match str_after_err.find('\n') {
                        Some(mut newline3) => {
                            newline3 += str_before_err.len();
                            // Print both lines, then the error.
                            println!("{}", &orig[newline2..newline1]);
                            println!("{}", &orig[newline1..newline3]);
                            let caret_line = " ".repeat(loc-newline1);
                            println!("{caret_line}^");
                            println!();
                            println!("{}", error.to_string());
                        },
                        None => {
                            // Print both lines, then the error.
                            println!("{}", &orig[newline2..newline1]);
                            println!("{}", &orig[newline1..]);
                            let caret_line = " ".repeat(loc-newline1);
                            println!("{caret_line}^");
                            println!();
                            println!("{}", error.to_string());
                        }
                    }
                },
                None => {
                    // Now find the newline after the error.
                    match str_after_err.find('\n') {
                        Some(mut newline3) => {
                            newline3 += str_before_err.len();
                            // Print the line, then the error.
                            println!("{}", &orig[newline1..newline3]);
                            let caret_line = " ".repeat(loc-newline1);
                            println!("{caret_line}^");
                            println!();
                            println!("{}", error.to_string());
                        },
                        None => {
                            // Print the line, then the error.
                            println!("{}", &orig[newline1..]);
                            let caret_line = " ".repeat(loc-newline1);
                            println!("{caret_line}^");
                            println!();
                            println!("{}", error.to_string());
                        }
                    }
                }
            }
        }
        None => {
            // there is no newline before the error.
            // just print the error line
            let line = orig.split('\n').next().unwrap_or_else(|| orig);
            println!("{}", line);
            let caret_line = " ".repeat(loc);
            println!("{caret_line}^");
            println!();
            println!("{}", error.to_string());
        }
    }
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

    fn trim(&mut self) {
        let mut len = 0;
        while self.input()[len..].starts_with(whitespace_char) {
            len += 1;
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
        let mut exprs: Vec<(Loc, Expr)> = vec![];
        loop {
            let loc = self.loc;
            match self.parse_expr_nested() {
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
                    match exprs.pop() {
                        None => { return Err(Error::ExpectedExpr(self.loc)); }
                        Some((_, f)) => {
                            let args = exprs.into_iter().map(|(_, e)| e).collect();
                            return Ok(Expr::App{head: Box::new(f), args});
                        }
                    }
                },
                Ok(expr) => {
                    exprs.push((loc, expr));
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
            self.eat(")")?;
            return self.parse_expr();
        }
        if self.input().starts_with(lower_ident_char) {
            let n = self.parse_lower_ident()?;
            return Ok(Expr::Var(Var::Local(n)));
        }
        if self.input().starts_with(upper_ident_char) {
            let n = self.parse_upper_ident()?;
            return Ok(Expr::Var(Var::Constructor(n)));
        }
        Err(Error::ExpectedExpr(self.loc))
    }

    fn parse_match(&mut self) -> Result<Expr, Error> {
        unimplemented!()
    }

    fn parse_int(&mut self) -> Result<Expr, Error> {
        unimplemented!()
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
        match self.input().match_indices(lower_ident_char).next() {
            Some((0, m)) => {
                let m = m.to_string();
                self.loc += m.len();
                Ok(m)
            },
            _ => {
                Err(Error::ExpectedLowerIdent(self.loc))
            }
        }
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

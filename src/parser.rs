use crate::ast::{
    Decl, Expr, HasLoc, Loc, MatchBranch, Operator, Pattern, SourceType, TypeConstructor, Var,
};
use std::collections::VecDeque;

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
    ExpectedType(Loc),
}

impl HasLoc for Error {
    fn loc(&self) -> Loc {
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
            Error::ExpectedType(loc) => *loc,
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Error::ExpectedLowerIdent(_) => {
                write!(f, "expected lowercase word")
            }
            Error::ExpectedUpperIdent(_) => {
                write!(f, "expected uppercase word")
            }
            Error::ExpectedNamedType(_) => {
                write!(f, "expected a named type")
            }
            Error::ExpectedExpr(_) => {
                write!(f, "expected an expression")
            }
            Error::ExpectedPattern(_) => {
                write!(f, "expected a pattern")
            }
            Error::ExpectedStr(s, _) => {
                write!(f, "expected '{}'", s)
            }
            Error::ExpectedOperator(_) => {
                write!(f, "expected '+' or '-' or '*'")
            }
            Error::ExpectedInteger(_) => {
                write!(f, "expected an integer")
            }
            Error::UnexpectedEof(_) => {
                write!(f, "unexpected EOF")
            }
            Error::ExpectedType(_) => {
                write!(f, "expected a type")
            }
        }
    }
}

pub struct Parser {
    orig: String,
    loc: usize,
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
            None => Err(Error::ExpectedStr(s, (self.loc, self.loc))),
        }
    }

    fn eat_char(&mut self) -> Result<char, Error> {
        match self.input().chars().next() {
            Some(c) => {
                self.loc += 1;
                Ok(c)
            }
            None => Err(Error::UnexpectedEof((self.loc, self.loc))),
        }
    }

    fn trim(&mut self) {
        let mut len = 0;

        loop {
            // Skip line comments
            if self.input()[len..].starts_with("//") {
                while !self.input()[len..].starts_with('\n') {
                    len += 1;
                }
                len += 1;
            } else {
                if self.input()[len..].starts_with(whitespace_char) {
                    len += 1;
                } else {
                    break;
                }
            }
        }

        self.loc += len;
    }

    pub fn parse(&mut self) -> Result<Vec<Decl>, Error> {
        let mut decls = vec![];
        loop {
            self.trim();
            if self.input().is_empty() {
                break;
            }
            let decl = self.parse_decl()?;
            decls.push(decl);
        }
        Ok(decls)
    }

    fn parse_decl(&mut self) -> Result<Decl, Error> {
        let loc = self.loc;
        match self.try_eat("type") {
            Some(_) => {
                self.trim();
                let name = self.parse_upper_ident()?;
                self.trim();

                let mut params = vec![];
                while self.input().starts_with(lower_ident_char) {
                    let param = self.parse_lower_ident()?;
                    params.push(param);
                    self.trim();
                }

                self.eat("{")?;
                let mut constructors = vec![];
                loop {
                    self.trim();
                    match self.try_eat("}") {
                        Some(_) => {
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
                Ok(Decl::Type {
                    loc: (loc, self.loc),
                    name,
                    params,
                    constructors,
                })
            }
            None => match self.try_eat("test") {
                Some(_) => {
                    self.trim();
                    let name = self.parse_lower_ident()?;
                    self.trim();
                    self.eat("{")?;
                    self.trim();
                    let body = self.parse_expr()?;
                    self.trim();
                    self.eat("}")?;
                    self.trim();
                    Ok(Decl::Test {
                        loc: (loc, self.loc),
                        name,
                        body,
                    })
                }
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
                    self.trim();
                    self.eat("}")?;
                    self.trim();
                    Ok(Decl::Func {
                        loc: (loc, self.loc),
                        name,
                        r#type,
                        body,
                    })
                }
            },
        }
    }

    fn parse_type(&mut self) -> Result<SourceType, Error> {
        // Parse a sequence of "type components", which are things that can make up a type.
        // We then construct the actual type from this sequence.
        // This allows us to deal with arrows and type applications.
        let mut components = VecDeque::new();
        loop {
            match self.try_parse_type_component() {
                Some(c) => {
                    components.push_back(c);
                }
                None => {
                    break;
                }
            }
            self.trim();
        }

        if components.is_empty() {
            return Err(Error::ExpectedType((self.loc, self.loc)));
        }

        // Now convert the list of components into a type.
        self.make_type_from_components(components)
    }

    // Like `parse_type`, but in a context where multi-word types must be parenthesised.
    // e.g.
    // Bool
    // (Bool -> Bool)
    // (Foo Bar)
    // (Foo -> Bar Baz)
    fn parse_type_nested(&mut self) -> Result<SourceType, Error> {
        if self.input().starts_with("(") {
            // Parse a normal type
            self.eat("(")?;
            self.trim();
            let ty = self.parse_type()?;
            self.trim();
            self.eat(")")?;
            self.trim();
            return Ok(ty);
        } else {
            let loc = self.loc;
            if self.input().starts_with(upper_ident_char) {
                let type_name = self.parse_upper_ident()?;
                if type_name == "Int" {
                    Ok(SourceType::Int((loc, self.loc)))
                } else {
                    Ok(SourceType::Named((loc, self.loc), type_name))
                }
            } else {
                let type_var = self.parse_lower_ident()?;
                Ok(SourceType::Var((loc, self.loc), type_var))
            }
        }
    }

    fn make_type_from_components(
        &self,
        mut components: VecDeque<(Loc, TypeComponent)>,
    ) -> Result<SourceType, Error> {
        let ty = {
            let (loc, c) = components.pop_front().unwrap();
            self.make_type_from_single_component(loc, c)?
        };

        if components.is_empty() {
            return Ok(ty);
        }

        match components.pop_front() {
            Some((loc, c)) => match c {
                TypeComponent::Arrow => {
                    let rest = self.make_type_from_components(components)?;
                    Ok(SourceType::Func(loc, Box::new(ty), Box::new(rest)))
                }
                TypeComponent::Type(_) => {
                    // Note: this code is currently dead, because we don't support polymorphism and
                    // so there are no type applications.

                    // We have two non-arrow types in a row, so we're looking at a type
                    // application. Take components from the list until we reach the end or we
                    // reach an arrow.

                    // The first arg of the application is the component we've just popped.
                    let first_arg = self.make_type_from_single_component(loc, c)?;
                    let mut args = vec![first_arg];

                    loop {
                        let c = components.pop_front();
                        match c {
                            Some((_, TypeComponent::Arrow)) => {
                                break;
                            }
                            Some((loc, c)) => {
                                let c_ty = self.make_type_from_single_component(loc, c)?;
                                args.push(c_ty);
                            }
                            None => {
                                break;
                            }
                        }
                    }
                    let app = SourceType::App {
                        loc: ty.loc(),
                        head: Box::new(ty),
                        args,
                    };

                    // If there are components left, then we have just parsed a type application to
                    // the left of an arrow.
                    if !components.is_empty() {
                        let rest = self.make_type_from_components(components)?;
                        Ok(SourceType::Func(loc, Box::new(app), Box::new(rest)))
                    } else {
                        // Otherwise, we're done and the result is the application.
                        Ok(app)
                    }
                }
            },
            None => Ok(ty),
        }
    }

    fn make_type_from_single_component(
        &self,
        loc: Loc,
        component: TypeComponent,
    ) -> Result<SourceType, Error> {
        match component {
            TypeComponent::Arrow => Err(Error::ExpectedNamedType(loc)),
            TypeComponent::Type(t) => Ok(t),
        }
    }

    fn try_parse_type_component(&mut self) -> Option<(Loc, TypeComponent)> {
        let loc = self.loc;
        if self.input().starts_with("->") {
            self.eat("->").unwrap();
            return Some(((loc, self.loc), TypeComponent::Arrow));
        }

        match self.parse_type_nested() {
            Err(_) => None,
            Ok(ty) => Some(((loc, self.loc), TypeComponent::Type(ty))),
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, Error> {
        if self.input().starts_with(numeric_char) {
            let (loc, n) = self.parse_int()?;
            return Ok(Expr::Int(loc, n));
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
        let mut exprs: VecDeque<Expr> = VecDeque::new();
        loop {
            let loc = self.loc;
            match self.parse_expr_nested() {
                Err(_) => {
                    // We've found a non-expression, so stop parsing.
                    // Check if it's an arrow.
                    if self.input().starts_with("->") {
                        // Check that the preceding expressions are patterns
                        let mut args = vec![];
                        for e in exprs {
                            match e {
                                Expr::Var(loc, Var::Local(n)) => {
                                    args.push((loc, n));
                                }
                                _ => {
                                    return Err(Error::ExpectedPattern((loc, self.loc)));
                                }
                            }
                        }

                        // Consume the arrow
                        self.eat("->")?;
                        self.trim();

                        // Parse the function body
                        let body = self.parse_expr()?;
                        self.trim();

                        return Ok(Expr::Func {
                            loc: (loc, self.loc),
                            args,
                            body: Box::new(body),
                        });
                    }

                    // It's not an arrow, so the preceding expressions form an application
                    // Construct the application
                    match exprs.pop_front() {
                        None => {
                            return Err(Error::ExpectedExpr((self.loc, self.loc)));
                        }
                        Some(f) => {
                            let args: Vec<_> = exprs.into_iter().collect();
                            if args.is_empty() {
                                return Ok(f);
                            } else {
                                return Ok(Expr::App {
                                    loc: f.loc(),
                                    head: Box::new(f),
                                    args,
                                });
                            }
                        }
                    }
                }
                Ok(expr) => {
                    exprs.push_back(expr);
                    self.trim();
                }
            }
        }
    }

    /// Like `parse_expr` but functions and applications must be wrapped in parens.
    fn parse_expr_nested(&mut self) -> Result<Expr, Error> {
        if self.input().starts_with(numeric_char) {
            let (loc, n) = self.parse_int()?;
            return Ok(Expr::Int(loc, n));
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
        if self.input().starts_with(lower_ident_char) || self.input().starts_with(upper_ident_char)
        {
            let loc = self.loc;
            let var = self.parse_var_or_constructor()?;
            return Ok(Expr::Var((loc, self.loc), var));
        }
        if self.input().starts_with(operator_char) {
            // To ensure we don't parse x -> y as x - <parse error>
            if !self.input().starts_with("->") {
                let (loc, op) = self.parse_operator()?;
                return Ok(Expr::Var(loc, op));
            }
        }
        Err(Error::ExpectedExpr((self.loc, self.loc)))
    }

    fn parse_var_or_constructor(&mut self) -> Result<Var, Error> {
        let loc = self.loc;

        let mut leading_underscores = 0;
        while self.input().starts_with('_') {
            self.eat("_")?;
            leading_underscores += 1;
        }

        if self.input().starts_with(upper_ident_char) {
            let n = self.parse_upper_ident()?;
            let s = format!("{}{n}", "_".repeat(leading_underscores));
            return Ok(Var::Constructor(s));
        }

        if self.input().starts_with(lower_ident_char) {
            let n = self.parse_lower_ident()?;
            let s = format!("{}{n}", "_".repeat(leading_underscores));
            return Ok(Var::Local(s));
        }

        // If there are no more valid characters left, but we have parsed some underscores,
        // then the result is a local variable.
        if leading_underscores > 0 {
            let s = "_".repeat(leading_underscores);
            return Ok(Var::Local(s));
        } else {
            return Err(Error::ExpectedLowerIdent((loc, self.loc)));
        }
    }

    fn parse_match(&mut self) -> Result<Expr, Error> {
        let loc = self.loc;
        self.eat("match")?;
        self.trim();
        let target = self.parse_expr()?;
        self.trim();
        self.eat("{")?;
        self.trim();
        let mut branches = vec![];
        loop {
            if self.input().starts_with("}") {
                break;
            }
            let branch = self.parse_match_branch()?;
            self.trim();
            self.try_eat(",");
            branches.push(branch);
            self.trim();
        }
        self.eat("}")?;
        self.trim();
        Ok(Expr::Match {
            loc: (loc, self.loc),
            target: Box::new(target),
            branches,
        })
    }

    fn parse_match_branch(&mut self) -> Result<MatchBranch, Error> {
        let loc = self.loc;
        let pattern = self.parse_pattern()?;
        self.trim();
        self.eat("->")?;
        self.trim();
        let rhs = self.parse_expr()?;
        Ok(MatchBranch {
            loc: (loc, self.loc),
            pattern,
            rhs,
        })
    }

    fn parse_pattern(&mut self) -> Result<Pattern, Error> {
        // TODO: nested patterns in parens
        // TODO: var patterns
        if self.input().starts_with(numeric_char) {
            let (loc, value) = self.parse_int()?;
            self.trim();
            return Ok(Pattern::Int { loc, value });
        }

        if self.input().starts_with(lower_ident_char) {
            let loc = self.loc;
            let name = self.parse_lower_ident()?;
            if name == "_" {
                return Ok(Pattern::Wildcard {
                    loc: (loc, self.loc),
                });
            } else {
                return Ok(Pattern::Var {
                    loc: (loc, self.loc),
                    name,
                });
            }
        }

        let loc = self.loc;
        let name = self.parse_upper_ident()?;
        self.trim();
        let mut args = vec![];
        loop {
            if self.input().starts_with("->") {
                break;
            }
            let pattern = self.parse_pattern_nested()?;
            args.push(pattern);
            self.trim();
        }
        Ok(Pattern::Constructor {
            loc: (loc, self.loc),
            name,
            args,
        })
    }

    fn parse_pattern_nested(&mut self) -> Result<Pattern, Error> {
        if self.input().starts_with(numeric_char) {
            let (loc, value) = self.parse_int()?;
            self.trim();
            return Ok(Pattern::Int { loc, value });
        }
        if self.input().starts_with(lower_ident_char) {
            let loc = self.loc;
            let name = self.parse_lower_ident()?;
            if name == "_" {
                return Ok(Pattern::Wildcard {
                    loc: (loc, self.loc),
                });
            } else {
                return Ok(Pattern::Var {
                    loc: (loc, self.loc),
                    name,
                });
            }
        }

        let loc = self.loc;
        let name = self.parse_upper_ident()?;
        self.trim();
        Ok(Pattern::Constructor {
            loc: (loc, self.loc),
            name,
            args: vec![],
        })
    }

    fn parse_int(&mut self) -> Result<(Loc, i64), Error> {
        let loc = self.loc;
        let mut len = 0;
        while self.input()[len..].starts_with(char::is_numeric) {
            len += 1;
        }

        let (s, _) = self.input().split_at(len);
        match s.parse() {
            Ok(n) => {
                self.loc += len;
                Ok(((loc, self.loc), n))
            }
            Err(_) => Err(Error::ExpectedInteger((loc, self.loc))),
        }
    }

    fn parse_operator(&mut self) -> Result<(Loc, Var), Error> {
        let op = self.eat_char()?;
        let op = match op {
            '+' => Operator::Add,
            '-' => Operator::Sub,
            '*' => Operator::Mul,
            _ => {
                return Err(Error::ExpectedOperator((self.loc - 1, self.loc - 1)));
            }
        };
        Ok(((self.loc - 1, self.loc - 1), Var::Operator(op)))
    }

    fn parse_type_constructor(&mut self) -> Result<TypeConstructor, Error> {
        let loc = self.loc;
        let name = self.parse_upper_ident()?;
        self.trim();
        let mut arguments = vec![];
        loop {
            if self.input().starts_with(upper_ident_char)
                || self.input().starts_with(lower_ident_char)
                || self.input().starts_with("(")
            {
                let arg = self.parse_type_nested()?;
                self.trim();
                arguments.push(arg);
            } else {
                break;
            }
        }
        Ok(TypeConstructor {
            loc: (loc, self.loc),
            name,
            variables: vec![],
            arguments,
        })
    }

    /// Parse an uppercase identifier.
    /// It must start with an uppercase letter or underscore, followed by zero or more alphanumeric
    /// chars or underscores.
    fn parse_upper_ident(&mut self) -> Result<String, Error> {
        if !self.input().starts_with(upper_ident_char) {
            return Err(Error::ExpectedUpperIdent((self.loc, self.loc)));
        }

        let mut len = 1;

        while self.input()[len..].starts_with(alphanum_or_underscore_char) {
            len += 1;
        }

        let (m, _) = self.input().split_at(len);
        let m = m.to_string();
        self.loc += len;
        Ok(m)
    }

    /// Parse a lowercase identifier.
    /// It must start with a lowercase letter or underscore, followed by zero or more alphanumeric
    /// chars or underscores.
    fn parse_lower_ident(&mut self) -> Result<String, Error> {
        if !self.input().starts_with(lower_ident_char) {
            return Err(Error::ExpectedLowerIdent((self.loc, self.loc)));
        }

        let mut len = 1;

        while self.input()[len..].starts_with(alphanum_or_underscore_char) {
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

fn alphanum_or_underscore_char(c: char) -> bool {
    c == '_' || (c >= 'A' && c <= 'z') || (c >= '0' && c <= '9')
}

fn whitespace_char(c: char) -> bool {
    c == ' ' || c == '\n'
}

fn numeric_char(c: char) -> bool {
    c >= '0' && c <= '9'
}

fn operator_char(c: char) -> bool {
    c == '+' || c == '-' || c == '*'
}

#[derive(Debug)]
enum TypeComponent {
    Arrow,
    Type(SourceType),
}

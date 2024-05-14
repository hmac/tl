use crate::ast::{
    CaseBranch, Decl, Expr, HasLoc, LetBinding, Loc, Operator, Pattern, SourceType,
    TypeConstructor, Var,
};
use std::{collections::VecDeque, path::PathBuf};

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
    UnknownStringEscapeSequence(Loc),
    FilePathIsNotRelative(Loc),
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
            Error::UnknownStringEscapeSequence(loc) => *loc,
            Error::FilePathIsNotRelative(loc) => *loc,
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
            Error::UnknownStringEscapeSequence(_) => {
                write!(f, "unknown string escape sequence")
            }
            Error::FilePathIsNotRelative(_) => {
                write!(f, "file path must be relative")
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
                None => match self.try_eat("use") {
                    Some(_) => {
                        self.trim();
                        let path_loc_start = self.loc;
                        let path = self.parse_relative_path()?;
                        let path_loc = (path_loc_start, self.loc);
                        self.trim();
                        self.eat("as")?;
                        self.trim();
                        let name_loc_start = self.loc;
                        let name = self.parse_lower_ident()?;
                        let name_loc = (name_loc_start, self.loc);
                        let r = Decl::Import {
                            loc: (loc, self.loc),
                            path,
                            path_loc,
                            name,
                            name_loc,
                        };
                        self.trim();
                        Ok(r)
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
            },
        }
    }

    fn parse_relative_path(&mut self) -> Result<PathBuf, Error> {
        let loc = self.loc;
        let mut len = 0;
        while !self.input()[len..].starts_with(char::is_whitespace) {
            len += 1;
        }

        let (s, _) = self.input().split_at(len);
        let path: PathBuf = s.parse().unwrap_or_else(|never| match never {});
        self.loc += len;
        let loc_end = self.loc;
        self.trim();

        if !path.is_relative() {
            Err(Error::FilePathIsNotRelative((loc, loc_end)))
        } else {
            Ok(path)
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

    // This identical to parse_tuple_or_parenthesised_expr but parses types instead of expressions.
    // Can we merge the two?
    fn parse_tuple_or_parenthesised_type(&mut self) -> Result<SourceType, Error> {
        let loc = self.loc;
        self.eat("(")?;
        self.trim();
        if self.input().starts_with(",") {
            // We are parsing unit (,) or there's a parse error
            self.eat(",")?;
            self.trim();
            self.eat(")")?;
            let r = SourceType::Tuple {
                loc: (loc, self.loc),
                elems: vec![],
            };
            self.trim();
            return Ok(r);
        } else {
            let elem1 = self.parse_type()?;
            self.trim();
            if self.input().starts_with(")") {
                // We've parsed a parenthesised expression
                self.eat(")")?;
                self.trim();
                Ok(elem1)
            } else {
                // We are parsing a tuple
                let mut elems = vec![elem1];
                loop {
                    self.trim();
                    if self.input().starts_with(")") {
                        break;
                    }
                    self.eat(",")?;
                    self.trim();
                    if self.input().starts_with(")") {
                        break;
                    }
                    elems.push(self.parse_type()?);
                }
                self.eat(")")?;
                let r = SourceType::Tuple {
                    loc: (loc, self.loc),
                    elems,
                };
                self.trim();
                Ok(r)
            }
        }
    }

    // Like `parse_type`, but in a context where multi-word types must be parenthesised.
    // e.g.
    // Bool
    // (Bool -> Bool)
    // (Foo Bar)
    // (Foo -> Bar Baz)
    // some_import.Foo
    fn parse_type_nested(&mut self) -> Result<SourceType, Error> {
        if self.input().starts_with("(") {
            return self.parse_tuple_or_parenthesised_type();
        } else {
            let loc = self.loc;

            // A leading underscore could be part of a namespace or a type.
            // Start by parsing all leading underscores, the add them on to the result of the next
            // parse.
            let mut leading_underscores = 0;
            while self.input().starts_with('_') {
                self.eat("_")?;
                leading_underscores += 1;
            }

            if self.input().starts_with(lower_ident_char) {
                let namespace_or_type_var = self.parse_lower_ident()?;
                let r = format!("{}{namespace_or_type_var}", "_".repeat(leading_underscores));
                leading_underscores = 0;

                // If the next char is ".", we have parsed a namespace.
                // Otherwise we've parsed a type variable.
                if self.input().starts_with(".") {
                    self.eat(".")?;

                    while self.input().starts_with('_') {
                        self.eat("_")?;
                        leading_underscores += 1;
                    }

                    let type_name = format!(
                        "{}{}",
                        "_".repeat(leading_underscores),
                        self.parse_upper_ident()?
                    );
                    Ok(SourceType::Named(
                        (loc, self.loc),
                        Some(r.into()),
                        type_name,
                    ))
                } else {
                    Ok(SourceType::Var((loc, self.loc), r))
                }
            } else {
                let type_name = format!(
                    "{}{}",
                    "_".repeat(leading_underscores),
                    self.parse_upper_ident()?
                );
                Ok(match type_name.as_str() {
                    "Int" => SourceType::Int((loc, self.loc)),
                    "Bool" => SourceType::Bool((loc, self.loc)),
                    "String" => SourceType::Str((loc, self.loc)),
                    "Char" => SourceType::Char((loc, self.loc)),
                    _ => SourceType::Named((loc, self.loc), None, type_name),
                })
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
                    if components.is_empty() {
                        Err(Error::ExpectedType((loc.1, loc.1)))
                    } else {
                        let rest = self.make_type_from_components(components)?;
                        Ok(SourceType::Func(loc, Box::new(ty), Box::new(rest)))
                    }
                }
                TypeComponent::Type(_) => {
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
        if let Some(expr) = self.maybe_parse_atomic_expr()? {
            return Ok(expr);
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

    /// Attempt to parse an expression which is totally unambiguous.
    /// This is shared code between `parsed_expr` and `parse_expr_nested` which handles expressions
    /// that have a unique leading character.
    fn maybe_parse_atomic_expr(&mut self) -> Result<Option<Expr>, Error> {
        if self.input().starts_with(numeric_char) {
            let (loc, n) = self.parse_int()?;
            return Ok(Some(Expr::Int(loc, n)));
        }
        if self.input().starts_with("case") {
            return self.parse_case().map(Some);
        }
        if self.input().starts_with("let") {
            return self.parse_let().map(Some);
        }
        if self.input().starts_with("[") {
            return self.parse_list().map(Some);
        }
        if self.input().starts_with("\"") {
            return self.parse_string().map(Some);
        }
        if self.input().starts_with("'") {
            return self.parse_char().map(Some);
        }
        if self.input().starts_with("(") {
            // The expression could be a tuple or a parenthesised expression
            return self.parse_tuple_or_parenthesised_expression().map(Some);
        }
        Ok(None)
    }

    /// Like `parse_expr` but functions and applications must be wrapped in parens.
    fn parse_expr_nested(&mut self) -> Result<Expr, Error> {
        if let Some(expr) = self.maybe_parse_atomic_expr()? {
            return Ok(expr);
        }
        if self.input().starts_with(lower_ident_char) || self.input().starts_with(upper_ident_char)
        {
            let loc = self.loc;
            let var = self.parse_var_or_constructor()?;
            let loc_end = self.loc;
            self.trim();
            return Ok(Expr::Var((loc, loc_end), var));
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

    fn parse_tuple_or_parenthesised_expression(&mut self) -> Result<Expr, Error> {
        let loc = self.loc;
        self.eat("(")?;
        self.trim();
        if self.input().starts_with(",") {
            // We are parsing unit (,) or there's a parse error
            self.eat(",")?;
            self.trim();
            self.eat(")")?;
            let r = Expr::Tuple {
                loc: (loc, self.loc),
                elems: vec![],
            };
            self.trim();
            return Ok(r);
        } else {
            let elem1 = self.parse_expr()?;
            self.trim();
            if self.input().starts_with(")") {
                // We've parsed a parenthesised expression
                self.eat(")")?;
                self.trim();
                Ok(elem1)
            } else {
                // We are parsing a tuple
                let mut elems = vec![elem1];
                loop {
                    self.trim();
                    if self.input().starts_with(")") {
                        break;
                    }
                    self.eat(",")?;
                    self.trim();
                    if self.input().starts_with(")") {
                        break;
                    }
                    elems.push(self.parse_expr()?);
                }
                self.eat(")")?;
                let r = Expr::Tuple {
                    loc: (loc, self.loc),
                    elems,
                };
                self.trim();
                Ok(r)
            }
        }
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
            return Ok(Var::Constructor(None, s));
        }

        if self.input().starts_with(lower_ident_char) {
            let n = self.parse_lower_ident()?;
            let s = format!("{}{n}", "_".repeat(leading_underscores));

            // If there's a dot, then we're parsing a namespaced constructor/variable
            if self.input().starts_with(".") {
                self.eat(".")?;

                let namespace = s;
                let loc = self.loc;

                let mut leading_underscores = 0;
                while self.input().starts_with('_') {
                    self.eat("_")?;
                    leading_underscores += 1;
                }

                if self.input().starts_with(upper_ident_char) {
                    let n = self.parse_upper_ident()?;
                    let s = format!("{}{n}", "_".repeat(leading_underscores));
                    return Ok(Var::Constructor(Some(namespace.into()), s));
                }

                if self.input().starts_with(lower_ident_char) {
                    let n = self.parse_lower_ident()?;
                    let v = format!("{}{n}", "_".repeat(leading_underscores));
                    return Ok(Var::Global(Some(namespace.into()), v));
                }

                // If we've reached here, we've parsed only some underscores,
                // with a namespace, e.g. foo.___
                // This is a weird name but it doesn't seem worth banning it right now.
                if leading_underscores > 0 {
                    let s = "_".repeat(leading_underscores);
                    return Ok(Var::Global(Some(namespace.into()), s));
                } else {
                    return Err(Error::ExpectedLowerIdent((loc, self.loc)));
                }
            }

            if s == "chars" {
                return Ok(Var::Operator(Operator::Chars));
            }

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

    /// Parse a list literal `[1, 2, 3]` or a list cons `[1, 2, ..x]`.
    fn parse_list(&mut self) -> Result<Expr, Error> {
        let loc = self.loc;
        self.eat("[")?;
        let mut elems = vec![];
        let mut tail = None;
        loop {
            self.trim();
            if self.input().starts_with("]") {
                break;
            }
            if self.input().starts_with("..") {
                self.eat("..")?;
                tail = Some(Box::new(self.parse_expr()?));
                break;
            }
            self.trim();
            elems.push(self.parse_expr()?);
            self.trim();
            self.try_eat(",");
        }
        self.eat("]")?;
        let result = Expr::List {
            loc: (loc, self.loc),
            elems,
            tail,
        };
        self.trim();
        Ok(result)
    }

    fn parse_let(&mut self) -> Result<Expr, Error> {
        let loc = self.loc;
        self.eat("let")?;
        self.trim();
        let mut bindings = vec![];
        loop {
            if self.input().starts_with("{") {
                break;
            }
            let loc = self.loc;
            let name = self.parse_lower_ident()?;
            self.trim();
            let ty = match self.try_eat(":") {
                None => None,
                Some(_) => {
                    self.trim();
                    let ty = self.parse_type()?;
                    Some(ty)
                }
            };
            self.eat("=")?;
            self.trim();
            let value = self.parse_expr()?;
            bindings.push(LetBinding {
                loc: (loc, self.loc),
                r#type: ty,
                name,
                value,
            });
            self.trim();
            self.try_eat(",");
            self.trim();
        }
        self.eat("{")?;
        self.trim();
        let body = self.parse_expr()?;
        self.trim();
        self.eat("}")?;
        let result = Expr::Let {
            loc: (self.loc, loc),
            bindings,
            body: Box::new(body),
        };
        self.trim();
        Ok(result)
    }

    fn parse_case(&mut self) -> Result<Expr, Error> {
        let loc = self.loc;
        self.eat("case")?;
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
        Ok(Expr::Case {
            loc: (loc, self.loc),
            target: Box::new(target),
            branches,
        })
    }

    fn parse_match_branch(&mut self) -> Result<CaseBranch, Error> {
        let loc = self.loc;
        let pattern = self.parse_pattern()?;
        self.trim();
        self.eat("->")?;
        self.trim();
        let rhs = self.parse_expr()?;
        Ok(CaseBranch {
            loc: (loc, self.loc),
            pattern,
            rhs,
        })
    }

    fn parse_pattern(&mut self) -> Result<Pattern, Error> {
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
                if self.input().starts_with(".") {
                    // We're parsing a namespaced constructor
                    self.eat(".")?;
                    let namespace = Some(name.into());
                    let name = self.parse_upper_ident()?;
                    self.trim();
                    return Ok(Pattern::Constructor {
                        loc: (loc, self.loc),
                        namespace,
                        name,
                        args: vec![],
                    });
                } else {
                    return Ok(Pattern::Var {
                        loc: (loc, self.loc),
                        name,
                    });
                }
            }
        }

        if self.input().starts_with("[") {
            let loc = self.loc;
            self.eat("[")?;
            let mut elems = vec![];
            let mut tail = None;
            loop {
                self.trim();
                if self.input().starts_with(".") || self.input().starts_with("]") {
                    break;
                }
                elems.push(self.parse_pattern()?);
                self.trim();
                self.try_eat(",");
            }
            if self.input().starts_with(".") {
                self.eat("..")?;
                tail = Some(Box::new(self.parse_pattern()?));
            }
            self.trim();
            self.eat("]")?;
            if elems.is_empty() && tail.is_none() {
                return Ok(Pattern::ListNil {
                    loc: (loc, self.loc),
                });
            } else {
                return Ok(Pattern::ListCons {
                    loc: (loc, self.loc),
                    elems,
                    tail,
                });
            }
        }

        if self.input().starts_with("(") {
            let loc = self.loc;
            self.eat("(")?;
            let mut elems = vec![];
            loop {
                self.trim();
                if self.input().starts_with(")") {
                    break;
                }
                elems.push(self.parse_pattern()?);
                self.trim();
                self.try_eat(",");
            }
            self.eat(")")?;
            let r = Pattern::Tuple {
                loc: (loc, self.loc),
                elems,
            };
            self.trim();
            return Ok(r);
        }

        let loc = self.loc;
        let name = self.parse_upper_ident()?;
        self.trim();
        let mut args = vec![];
        loop {
            if self.input().starts_with("->")
                || self.input().starts_with("]")
                || self.input().starts_with(",")
                || self.input().starts_with(")")
            {
                break;
            }
            let pattern = self.parse_pattern_nested()?;
            args.push(pattern);
            self.trim();
        }
        Ok(Pattern::Constructor {
            loc: (loc, self.loc),
            namespace: None,
            name,
            args,
        })
    }

    // Like `parse_pattern` but does not parse constructor patterns with arguments.
    // In other words, it only parses patterns that are unambiguous when used
    // inside a larger pattern.
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
                if self.input().starts_with(".") {
                    // We're parsing a namespaced constructor
                    self.eat(".")?;
                    let namespace = Some(name.into());
                    let name = self.parse_upper_ident()?;
                    self.trim();
                    return Ok(Pattern::Constructor {
                        loc: (loc, self.loc),
                        namespace,
                        name,
                        args: vec![],
                    });
                } else {
                    return Ok(Pattern::Var {
                        loc: (loc, self.loc),
                        name,
                    });
                }
            }
        }
        if self.input().starts_with("(") {
            self.eat("(")?;
            self.trim();
            let pat = self.parse_pattern()?;
            self.eat(")")?;
            self.trim();
            return Ok(pat);
        }

        let loc = self.loc;
        let name = self.parse_upper_ident()?;
        self.trim();
        Ok(Pattern::Constructor {
            loc: (loc, self.loc),
            namespace: None,
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
                let loc_end = self.loc;
                self.trim();
                Ok(((loc, loc_end), n))
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
            '=' => match self.eat_char()? {
                '=' => Operator::Eq,
                _ => return Err(Error::ExpectedOperator((self.loc - 2, self.loc - 1))),
            },
            '<' => Operator::Lt,
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

    fn parse_string(&mut self) -> Result<Expr, Error> {
        let loc = self.loc;
        self.eat("\"")?;
        let mut s = String::new();
        loop {
            let c = self.eat_char()?;
            if c == '\\' {
                let c2 = self.eat_char()?;
                if c2 == '"' {
                    s.push('"');
                } else if c2 == '\\' {
                    s.push('\\');
                } else {
                    return Err(Error::UnknownStringEscapeSequence((self.loc - 2, self.loc)));
                }
            } else if c == '"' {
                break;
            } else {
                s.push(c);
            }
        }
        let r = Expr::Str((loc, self.loc), s);
        self.trim();
        Ok(r)
    }

    fn parse_char(&mut self) -> Result<Expr, Error> {
        let loc = self.loc;
        self.eat("'")?;
        let c = self.eat_char()?;
        self.eat("'")?;
        let r = Expr::Char((loc, self.loc), c);
        self.trim();
        Ok(r)
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
    c == '_' || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
}

fn whitespace_char(c: char) -> bool {
    c == ' ' || c == '\n'
}

fn numeric_char(c: char) -> bool {
    c >= '0' && c <= '9'
}

fn operator_char(c: char) -> bool {
    c == '+' || c == '-' || c == '*' || c == '=' || c == '<'
}

#[derive(Debug)]
enum TypeComponent {
    Arrow,
    Type(SourceType),
}

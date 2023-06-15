use std::collections::HashMap;

/// A linked list of local variable maps.
/// This makes it easy to add new variables for typechecking a specific subexpression,
/// without affecting the variables in scope for the parent call.
#[derive(Debug)]
pub enum LocalVariables<'a, T> {
    One(HashMap<String, T>),
    More(HashMap<String, T>, &'a LocalVariables<'a, T>),
}

impl<'a, T> LocalVariables<'a, T> {
    pub fn new() -> Self {
        Self::One(HashMap::new())
    }

    pub fn lookup(&self, name: &str) -> Option<&T> {
        match self {
            Self::One(stack) => match stack.get(name) {
                Some(ty) => Some(ty),
                None => None,
            },
            Self::More(stack, rest) => match stack.get(name) {
                Some(ty) => Some(ty),
                None => rest.lookup(name),
            },
        }
    }

    pub fn extend(&'a self, stack: HashMap<String, T>) -> LocalVariables<'a, T> {
        Self::More(stack, &self)
    }

    pub fn names(&'a self) -> Vec<&String> {
        match self {
            Self::One(s) => s.keys().collect(),
            Self::More(s, r) => {
                let mut names = r.names();
                names.append(&mut s.keys().collect());
                names
            }
        }
    }
}

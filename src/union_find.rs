use std::iter::IntoIterator;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use union_find_rs::{disjoint_sets::DisjointSets, traits::UnionFind};

use crate::ast::Type;

type Key = usize;

/// Used to group type variables together if they represent the same type.
/// The choice of "representative" variable is effectively random, so we only store variables here.
/// We then have a map from the representative variable to a concrete type, if any.
pub struct TypeEqualitySet {
    // usize is a key into the types map
    inner: DisjointSets<Key>,
    type_to_key: HashMap<Type, Key>,
    key_to_type: Vec<Type>,
}

#[derive(Debug)]
struct TypeEqualitySetDebug {
    type_to_key: HashMap<Type, Key>,
    key_to_type: Vec<Type>,
}

impl TypeEqualitySetDebug {
    fn from(tes: &TypeEqualitySet) -> Self {
        Self {
            type_to_key: tes.type_to_key.clone(),
            key_to_type: tes.key_to_type.clone()
        }
    }
}

impl Debug for TypeEqualitySet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{:?}", TypeEqualitySetDebug::from(self))
    }
}

impl TypeEqualitySet {
    pub fn new() -> Self {
        Self {
            inner: DisjointSets::new(),
            type_to_key: HashMap::new(),
            key_to_type: vec![]
        }
    }

    pub fn unify(&mut self, t1: &Type, t2: &Type)  {
        // Find/create a key for each type
        let t1_k = self.find_or_insert_type(t1);
        let t2_k = self.find_or_insert_type(t2);

        self.inner.union(&t1_k, &t2_k).unwrap()
    }

    pub fn lookup(&mut self, t: &Type) -> Type {
        let k = self.find_or_insert_type(t);

        let k = self.inner.find_set(&k).unwrap();

        self.key_to_type[k].clone()
    }

    fn find_or_insert_type(&mut self, t: &Type) -> usize {
        match self.type_to_key.get(t) {
            Some(k) => *k,
            None => {
                let k = self.key_to_type.len();

                self.key_to_type.push((*t).clone());
                self.type_to_key.insert((*t).clone(), k);
                self.inner.make_set(k);

                k
            }
        }
    }
}

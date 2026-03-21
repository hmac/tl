use std::fmt;

use crate::ast;

/// A simplified pattern representation used by the exhaustiveness algorithm.
/// Unlike `ast::Pattern`, this has no source locations, no variable names,
/// and list patterns are desugared into Cons/Nil constructors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    /// Matches a specific constructor with sub-patterns for its arguments.
    Constructor { name: String, args: Vec<Pattern> },
    /// Matches anything.
    Wildcard,
    /// Matches a specific integer literal.
    IntLiteral(i64),
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::Wildcard => write!(f, "_"),
            Pattern::IntLiteral(n) => write!(f, "{n}"),
            Pattern::Constructor { name, args } if name == "Cons" && args.len() == 2 => {
                // Pretty-print list constructors back into list syntax
                let mut elems = vec![];
                let mut current = self;
                loop {
                    match current {
                        Pattern::Constructor { name, args } if name == "Cons" && args.len() == 2 => {
                            elems.push(&args[0]);
                            current = &args[1];
                        }
                        Pattern::Constructor { name, args } if name == "Nil" && args.is_empty() => {
                            // Proper list ending
                            write!(f, "[")?;
                            for (i, e) in elems.iter().enumerate() {
                                if i > 0 { write!(f, ", ")?; }
                                write!(f, "{e}")?;
                            }
                            return write!(f, "]");
                        }
                        tail => {
                            // List with a tail pattern
                            write!(f, "[")?;
                            for (i, e) in elems.iter().enumerate() {
                                if i > 0 { write!(f, ", ")?; }
                                write!(f, "{e}")?;
                            }
                            return write!(f, ", ..{tail}]");
                        }
                    }
                }
            }
            Pattern::Constructor { name, args } if name == "Nil" && args.is_empty() => {
                write!(f, "[]")
            }
            Pattern::Constructor { name, args } if name.starts_with("Tuple_") => {
                write!(f, "(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
            Pattern::Constructor { name, args } if args.is_empty() => {
                write!(f, "{name}")
            }
            Pattern::Constructor { name, args } => {
                write!(f, "{name}")?;
                for a in args {
                    match a {
                        Pattern::Constructor { args: inner_args, .. } if !inner_args.is_empty() => {
                            write!(f, " ({a})")?;
                        }
                        _ => write!(f, " {a}")?,
                    }
                }
                Ok(())
            }
        }
    }
}

/// Information about a single constructor: its name and arity (number of arguments).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorInfo {
    pub name: String,
    pub arity: usize,
}

/// Provides the exhaustiveness checker with information about types.
/// Given a constructor name, returns info about all sibling constructors
/// (i.e. all constructors of the same type).
pub trait ConstructorLookup {
    /// Given a constructor name, return all constructors of the type it belongs to.
    /// Returns None if the constructor is unknown (e.g. for integer literals).
    fn siblings(&self, constructor_name: &str) -> Option<Vec<ConstructorInfo>>;
}

/// Convert an `ast::Pattern` into the simplified `Pattern` used by this module.
pub fn from_ast_pattern(pat: &ast::Pattern) -> Pattern {
    match pat {
        ast::Pattern::Constructor { name, args, .. } => Pattern::Constructor {
            name: name.clone(),
            args: args.iter().map(from_ast_pattern).collect(),
        },
        ast::Pattern::Var { .. } | ast::Pattern::Wildcard { .. } => Pattern::Wildcard,
        ast::Pattern::Int { value, .. } => Pattern::IntLiteral(*value),
        ast::Pattern::ListNil { .. } => Pattern::Constructor {
            name: "Nil".to_string(),
            args: vec![],
        },
        ast::Pattern::ListCons { elems, tail, .. } => {
            // Desugar [a, b, c, ..t] into Cons(a, Cons(b, Cons(c, t)))
            // and [a, b, c] into Cons(a, Cons(b, Cons(c, Nil)))
            let tail_pat = match tail {
                Some(t) => from_ast_pattern(t),
                None => Pattern::Constructor {
                    name: "Nil".to_string(),
                    args: vec![],
                },
            };
            elems.iter().rev().fold(tail_pat, |acc, elem| Pattern::Constructor {
                name: "Cons".to_string(),
                args: vec![from_ast_pattern(elem), acc],
            })
        }
        ast::Pattern::Tuple { elems, .. } => Pattern::Constructor {
            name: format!("Tuple_{}", elems.len()),
            args: elems.iter().map(from_ast_pattern).collect(),
        },
    }
}

/// Check whether a set of branch patterns exhaustively covers a type.
/// Returns the list of uncovered patterns (empty means exhaustive).
pub fn check_exhaustiveness(
    branches: &[Pattern],
    lookup: &dyn ConstructorLookup,
) -> Vec<Pattern> {
    let mut uncovered = vec![Pattern::Wildcard];

    for branch in branches {
        uncovered = uncovered
            .into_iter()
            .flat_map(|q| subtract(&q, branch, lookup))
            .collect();
    }

    uncovered
}

/// Subtract pattern `branch` from `uncovered`, returning the set of values
/// matched by `uncovered` but NOT matched by `branch`.
fn subtract(
    uncovered: &Pattern,
    branch: &Pattern,
    lookup: &dyn ConstructorLookup,
) -> Vec<Pattern> {
    match (uncovered, branch) {
        // Wildcard branch covers everything
        (_, Pattern::Wildcard) => vec![],

        // Integer literals: we can't enumerate all ints, so be conservative
        (Pattern::IntLiteral(n), Pattern::IntLiteral(m)) => {
            if n == m {
                vec![]
            } else {
                vec![uncovered.clone()]
            }
        }
        (Pattern::Wildcard, Pattern::IntLiteral(_)) => {
            // We can't expand Wildcard into all integers.
            // Remain conservative: report as still uncovered.
            vec![Pattern::Wildcard]
        }

        // Wildcard uncovered, constructor branch: expand into all constructors
        (Pattern::Wildcard, Pattern::Constructor { name, args }) => {
            match lookup.siblings(name) {
                None => {
                    // Unknown type, be conservative
                    vec![Pattern::Wildcard]
                }
                Some(ctors) => {
                    let mut result = vec![];
                    for ctor in &ctors {
                        if ctor.name == *name {
                            // Same constructor: recurse on children
                            let wildcard_args: Vec<Pattern> =
                                (0..ctor.arity).map(|_| Pattern::Wildcard).collect();
                            let residuals =
                                subtract_children(&wildcard_args, args, lookup);
                            for child_args in residuals {
                                result.push(Pattern::Constructor {
                                    name: ctor.name.clone(),
                                    args: child_args,
                                });
                            }
                        } else {
                            // Different constructor: entirely uncovered
                            result.push(Pattern::Constructor {
                                name: ctor.name.clone(),
                                args: vec![Pattern::Wildcard; ctor.arity],
                            });
                        }
                    }
                    result
                }
            }
        }

        // Same constructor: recurse on children
        (
            Pattern::Constructor {
                name: name_u,
                args: args_u,
            },
            Pattern::Constructor {
                name: name_b,
                args: args_b,
            },
        ) if name_u == name_b => {
            let residuals = subtract_children(args_u, args_b, lookup);
            residuals
                .into_iter()
                .map(|child_args| Pattern::Constructor {
                    name: name_u.clone(),
                    args: child_args,
                })
                .collect()
        }

        // Different constructors: branch doesn't cover uncovered at all
        (
            Pattern::Constructor { .. },
            Pattern::Constructor { .. },
        ) => vec![uncovered.clone()],

        // Constructor uncovered, integer branch (or vice versa): no overlap
        (Pattern::Constructor { .. }, Pattern::IntLiteral(_))
        | (Pattern::IntLiteral(_), Pattern::Constructor { .. }) => {
            vec![uncovered.clone()]
        }
    }
}

/// Given uncovered child patterns and branch child patterns (same constructor, same length),
/// return the residual child pattern combinations not covered by the branch.
///
/// For example, if uncovered is `(_, _)` and branch is `(True, _)` on type `(Bool, X)`:
/// - Position 0: subtract(_, True) -> [False]
/// - Position 1: subtract(_, _) -> []
///
/// We produce residuals by "fanning out": for each position i where subtraction yields
/// residuals, emit patterns with the residual at position i and the original uncovered
/// patterns at all other positions.
fn subtract_children(
    uncovered_args: &[Pattern],
    branch_args: &[Pattern],
    lookup: &dyn ConstructorLookup,
) -> Vec<Vec<Pattern>> {
    assert_eq!(uncovered_args.len(), branch_args.len());

    let mut result = vec![];

    for i in 0..uncovered_args.len() {
        let residuals_at_i = subtract(&uncovered_args[i], &branch_args[i], lookup);

        for residual in residuals_at_i {
            // Build a child pattern vector: original uncovered at positions before i,
            // the residual at position i, and wildcards at positions after i.
            // Using wildcards after i (rather than uncovered_args) is correct because
            // the residual at position i already restricts the space, and we'll handle
            // positions after i in subsequent iterations.
            let mut child = Vec::with_capacity(uncovered_args.len());
            for j in 0..uncovered_args.len() {
                if j < i {
                    child.push(uncovered_args[j].clone());
                } else if j == i {
                    child.push(residual.clone());
                } else {
                    // Use wildcard for positions after i to avoid over-restricting.
                    // The branch pattern at position j is already handled when i == j
                    // in a later iteration.
                    child.push(uncovered_args[j].clone());
                }
            }
            result.push(child);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- Test helpers --

    /// A simple in-memory constructor lookup for tests.
    struct TestLookup {
        /// Maps constructor name -> list of all constructors for that type
        types: Vec<Vec<ConstructorInfo>>,
    }

    impl TestLookup {
        fn new(types: Vec<Vec<ConstructorInfo>>) -> Self {
            Self { types }
        }
    }

    impl ConstructorLookup for TestLookup {
        fn siblings(&self, constructor_name: &str) -> Option<Vec<ConstructorInfo>> {
            for ctors in &self.types {
                if ctors.iter().any(|c| c.name == constructor_name) {
                    return Some(ctors.clone());
                }
            }
            None
        }
    }

    fn ctor(name: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::Constructor {
            name: name.to_string(),
            args,
        }
    }

    fn w() -> Pattern {
        Pattern::Wildcard
    }

    fn bool_type() -> Vec<ConstructorInfo> {
        vec![
            ConstructorInfo { name: "True".to_string(), arity: 0 },
            ConstructorInfo { name: "False".to_string(), arity: 0 },
        ]
    }

    fn option_type() -> Vec<ConstructorInfo> {
        vec![
            ConstructorInfo { name: "Some".to_string(), arity: 1 },
            ConstructorInfo { name: "None".to_string(), arity: 0 },
        ]
    }

    fn list_type() -> Vec<ConstructorInfo> {
        vec![
            ConstructorInfo { name: "Cons".to_string(), arity: 2 },
            ConstructorInfo { name: "Nil".to_string(), arity: 0 },
        ]
    }

    fn ordering_type() -> Vec<ConstructorInfo> {
        vec![
            ConstructorInfo { name: "Lt".to_string(), arity: 0 },
            ConstructorInfo { name: "Eq".to_string(), arity: 0 },
            ConstructorInfo { name: "Gt".to_string(), arity: 0 },
        ]
    }

    fn pair_type() -> Vec<ConstructorInfo> {
        vec![
            ConstructorInfo { name: "Tuple_2".to_string(), arity: 2 },
        ]
    }

    fn lookup_with(types: Vec<Vec<ConstructorInfo>>) -> TestLookup {
        TestLookup::new(types)
    }

    // -- Unit tests --

    #[test]
    fn wildcard_vs_single_constructor() {
        // subtract(_, Some _) on Option should leave [None]
        let lookup = lookup_with(vec![option_type()]);
        let result = subtract(&w(), &ctor("Some", vec![w()]), &lookup);
        assert_eq!(result, vec![ctor("None", vec![])]);
    }

    #[test]
    fn full_coverage_all_constructors() {
        // Subtracting all constructors from wildcard leaves nothing
        let lookup = lookup_with(vec![option_type()]);
        let result = check_exhaustiveness(
            &[ctor("Some", vec![w()]), ctor("None", vec![])],
            &lookup,
        );
        assert_eq!(result, vec![]);
    }

    #[test]
    fn nested_option_bool() {
        // case { Some True -> ..., None -> ... } should leave [Some False]
        let lookup = lookup_with(vec![option_type(), bool_type()]);
        let result = check_exhaustiveness(
            &[ctor("Some", vec![ctor("True", vec![])]), ctor("None", vec![])],
            &lookup,
        );
        assert_eq!(result, vec![ctor("Some", vec![ctor("False", vec![])])]);
    }

    #[test]
    fn nested_option_bool_exhaustive() {
        // case { Some True -> ..., Some False -> ..., None -> ... } is exhaustive
        let lookup = lookup_with(vec![option_type(), bool_type()]);
        let result = check_exhaustiveness(
            &[
                ctor("Some", vec![ctor("True", vec![])]),
                ctor("Some", vec![ctor("False", vec![])]),
                ctor("None", vec![]),
            ],
            &lookup,
        );
        assert_eq!(result, vec![]);
    }

    #[test]
    fn same_constructor_different_children() {
        // subtract(Some True, Some False) should leave [Some True]
        let lookup = lookup_with(vec![option_type(), bool_type()]);
        let result = subtract(
            &ctor("Some", vec![ctor("True", vec![])]),
            &ctor("Some", vec![ctor("False", vec![])]),
            &lookup,
        );
        assert_eq!(result, vec![ctor("Some", vec![ctor("True", vec![])])]);
    }

    #[test]
    fn different_constructors_no_subtraction() {
        // subtract(None, Some _) should leave [None]
        let lookup = lookup_with(vec![option_type()]);
        let result = subtract(
            &ctor("None", vec![]),
            &ctor("Some", vec![w()]),
            &lookup,
        );
        assert_eq!(result, vec![ctor("None", vec![])]);
    }

    #[test]
    fn wildcard_branch_covers_everything() {
        // subtract(Some True, _) should leave []
        let lookup = lookup_with(vec![option_type(), bool_type()]);
        let result = subtract(
            &ctor("Some", vec![ctor("True", vec![])]),
            &w(),
            &lookup,
        );
        assert_eq!(result, vec![]);
    }

    #[test]
    fn integer_literal_same() {
        let lookup = lookup_with(vec![]);
        let result = subtract(&Pattern::IntLiteral(42), &Pattern::IntLiteral(42), &lookup);
        assert_eq!(result, vec![]);
    }

    #[test]
    fn integer_literal_different() {
        let lookup = lookup_with(vec![]);
        let result = subtract(&Pattern::IntLiteral(42), &Pattern::IntLiteral(7), &lookup);
        assert_eq!(result, vec![Pattern::IntLiteral(42)]);
    }

    #[test]
    fn integer_wildcard_conservative() {
        // We can't enumerate ints, so Wildcard stays uncovered
        let lookup = lookup_with(vec![]);
        let result = subtract(&w(), &Pattern::IntLiteral(0), &lookup);
        assert_eq!(result, vec![w()]);
    }

    #[test]
    fn list_cons_and_nil_exhaustive() {
        // [_, .._] and [] covers List
        let lookup = lookup_with(vec![list_type()]);
        let result = check_exhaustiveness(
            &[ctor("Cons", vec![w(), w()]), ctor("Nil", vec![])],
            &lookup,
        );
        assert_eq!(result, vec![]);
    }

    #[test]
    fn list_missing_nil() {
        // [_, .._] alone leaves [] uncovered
        let lookup = lookup_with(vec![list_type()]);
        let result = check_exhaustiveness(
            &[ctor("Cons", vec![w(), w()])],
            &lookup,
        );
        assert_eq!(result, vec![ctor("Nil", vec![])]);
    }

    #[test]
    fn list_missing_cons() {
        // [] alone leaves [_, .._] uncovered
        let lookup = lookup_with(vec![list_type()]);
        let result = check_exhaustiveness(
            &[ctor("Nil", vec![])],
            &lookup,
        );
        assert_eq!(result, vec![ctor("Cons", vec![w(), w()])]);
    }

    #[test]
    fn tuple_bool_bool_partial() {
        // (True, True) on (Bool, Bool) leaves (False, _) and (_, False)
        // These two together cover exactly the complement of (True, True)
        let lookup = lookup_with(vec![pair_type(), bool_type()]);
        let result = check_exhaustiveness(
            &[ctor("Tuple_2", vec![ctor("True", vec![]), ctor("True", vec![])])],
            &lookup,
        );
        assert_eq!(result, vec![
            ctor("Tuple_2", vec![ctor("False", vec![]), w()]),
            ctor("Tuple_2", vec![w(), ctor("False", vec![])]),
        ]);
    }

    #[test]
    fn tuple_bool_bool_exhaustive() {
        let lookup = lookup_with(vec![pair_type(), bool_type()]);
        let result = check_exhaustiveness(
            &[
                ctor("Tuple_2", vec![ctor("True", vec![]), ctor("True", vec![])]),
                ctor("Tuple_2", vec![ctor("True", vec![]), ctor("False", vec![])]),
                ctor("Tuple_2", vec![ctor("False", vec![]), w()]),
            ],
            &lookup,
        );
        assert_eq!(result, vec![]);
    }

    #[test]
    fn three_constructors() {
        // Missing Gt from Ordering
        let lookup = lookup_with(vec![ordering_type()]);
        let result = check_exhaustiveness(
            &[ctor("Lt", vec![]), ctor("Eq", vec![])],
            &lookup,
        );
        assert_eq!(result, vec![ctor("Gt", vec![])]);
    }

    #[test]
    fn deep_nesting() {
        // Option (Option Bool): case { Some (Some True) -> ..., None -> ... }
        // Should leave: Some (Some False), Some None
        let lookup = lookup_with(vec![option_type(), bool_type()]);
        let result = check_exhaustiveness(
            &[
                ctor("Some", vec![ctor("Some", vec![ctor("True", vec![])])]),
                ctor("None", vec![]),
            ],
            &lookup,
        );
        assert_eq!(result, vec![
            ctor("Some", vec![ctor("Some", vec![ctor("False", vec![])])]),
            ctor("Some", vec![ctor("None", vec![])]),
        ]);
    }

    #[test]
    fn wildcard_only_is_exhaustive() {
        let lookup = lookup_with(vec![option_type()]);
        let result = check_exhaustiveness(&[w()], &lookup);
        assert_eq!(result, vec![]);
    }

    #[test]
    fn empty_branches_not_exhaustive() {
        let lookup = lookup_with(vec![option_type()]);
        let result = check_exhaustiveness(&[], &lookup);
        assert_eq!(result, vec![w()]);
    }

    #[test]
    fn list_nested_option() {
        // case { [Some _, .._] -> ..., [] -> ... }
        // Missing: [None, .._]
        let lookup = lookup_with(vec![list_type(), option_type()]);
        let result = check_exhaustiveness(
            &[
                ctor("Cons", vec![ctor("Some", vec![w()]), w()]),
                ctor("Nil", vec![]),
            ],
            &lookup,
        );
        assert_eq!(result, vec![
            ctor("Cons", vec![ctor("None", vec![]), w()]),
        ]);
    }

    #[test]
    fn from_ast_pattern_list_cons() {
        // [x, y, ..z] should desugar to Cons(_, Cons(_, _))
        let ast_pat = ast::Pattern::ListCons {
            loc: (0, 0),
            elems: vec![
                ast::Pattern::Var { loc: (0, 0), name: "x".to_string() },
                ast::Pattern::Var { loc: (0, 0), name: "y".to_string() },
            ],
            tail: Some(Box::new(ast::Pattern::Var { loc: (0, 0), name: "z".to_string() })),
        };
        let result = from_ast_pattern(&ast_pat);
        assert_eq!(result, ctor("Cons", vec![w(), ctor("Cons", vec![w(), w()])]));
    }

    #[test]
    fn from_ast_pattern_list_no_tail() {
        // [x, y] should desugar to Cons(_, Cons(_, Nil))
        let ast_pat = ast::Pattern::ListCons {
            loc: (0, 0),
            elems: vec![
                ast::Pattern::Var { loc: (0, 0), name: "x".to_string() },
                ast::Pattern::Var { loc: (0, 0), name: "y".to_string() },
            ],
            tail: None,
        };
        let result = from_ast_pattern(&ast_pat);
        assert_eq!(
            result,
            ctor("Cons", vec![w(), ctor("Cons", vec![w(), ctor("Nil", vec![])])])
        );
    }

    #[test]
    fn from_ast_pattern_tuple() {
        let ast_pat = ast::Pattern::Tuple {
            loc: (0, 0),
            elems: vec![
                ast::Pattern::Wildcard { loc: (0, 0) },
                ast::Pattern::Wildcard { loc: (0, 0) },
            ],
        };
        let result = from_ast_pattern(&ast_pat);
        assert_eq!(result, ctor("Tuple_2", vec![w(), w()]));
    }

    #[test]
    fn from_ast_pattern_nil() {
        let ast_pat = ast::Pattern::ListNil { loc: (0, 0) };
        let result = from_ast_pattern(&ast_pat);
        assert_eq!(result, ctor("Nil", vec![]));
    }

    #[test]
    fn display_simple_constructor() {
        assert_eq!(format!("{}", ctor("None", vec![])), "None");
        assert_eq!(format!("{}", ctor("Some", vec![w()])), "Some _");
        assert_eq!(
            format!("{}", ctor("Some", vec![ctor("True", vec![])])),
            "Some True"
        );
    }

    #[test]
    fn display_nested_constructor() {
        let pat = ctor("Some", vec![ctor("Some", vec![ctor("False", vec![])])]);
        assert_eq!(format!("{pat}"), "Some (Some False)");
    }

    #[test]
    fn display_list() {
        // Cons(_, Cons(_, Nil)) -> [_, _]
        let pat = ctor("Cons", vec![w(), ctor("Cons", vec![w(), ctor("Nil", vec![])])]);
        assert_eq!(format!("{pat}"), "[_, _]");
    }

    #[test]
    fn display_list_with_tail() {
        // Cons(_, _) -> [_, .._]
        let pat = ctor("Cons", vec![w(), w()]);
        assert_eq!(format!("{pat}"), "[_, .._]");
    }

    #[test]
    fn display_empty_list() {
        assert_eq!(format!("{}", ctor("Nil", vec![])), "[]");
    }

    #[test]
    fn display_tuple() {
        let pat = ctor("Tuple_2", vec![ctor("True", vec![]), w()]);
        assert_eq!(format!("{pat}"), "(True, _)");
    }
}

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;

    /// A type identifier used during generation.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct TypeId(usize);

    /// A generated type environment: a list of types, each with its constructors.
    /// Constructor arguments refer to types by TypeId.
    #[derive(Debug, Clone)]
    struct TypeEnv {
        types: Vec<Vec<GenConstructor>>,
    }

    #[derive(Debug, Clone)]
    struct GenConstructor {
        name: String,
        /// Each argument is a TypeId referencing a type in the environment.
        arg_types: Vec<TypeId>,
    }

    impl ConstructorLookup for TypeEnv {
        fn siblings(&self, constructor_name: &str) -> Option<Vec<ConstructorInfo>> {
            for ctors in &self.types {
                if ctors.iter().any(|c| c.name == constructor_name) {
                    return Some(
                        ctors
                            .iter()
                            .map(|c| ConstructorInfo {
                                name: c.name.clone(),
                                arity: c.arg_types.len(),
                            })
                            .collect(),
                    );
                }
            }
            None
        }
    }

    impl TypeEnv {
        fn constructors_of(&self, ty: TypeId) -> &[GenConstructor] {
            &self.types[ty.0]
        }
    }

    /// Generate all exhaustive leaf patterns for a type, expanding constructors
    /// to the given depth. At depth 0, returns [Wildcard].
    fn generate_exhaustive_patterns(
        env: &TypeEnv,
        ty: TypeId,
        depth: usize,
    ) -> Vec<Pattern> {
        if depth == 0 {
            return vec![Pattern::Wildcard];
        }
        let ctors = env.constructors_of(ty);
        let mut result = vec![];
        for ctor in ctors {
            let arg_pattern_sets: Vec<Vec<Pattern>> = ctor
                .arg_types
                .iter()
                .map(|arg_ty| generate_exhaustive_patterns(env, *arg_ty, depth - 1))
                .collect();
            for combo in cartesian_product(&arg_pattern_sets) {
                result.push(Pattern::Constructor {
                    name: ctor.name.clone(),
                    args: combo,
                });
            }
        }
        result
    }

    fn cartesian_product(sets: &[Vec<Pattern>]) -> Vec<Vec<Pattern>> {
        if sets.is_empty() {
            return vec![vec![]];
        }
        let mut result = vec![vec![]];
        for set in sets {
            let mut new_result = vec![];
            for existing in &result {
                for item in set {
                    let mut combo = existing.clone();
                    combo.push(item.clone());
                    new_result.push(combo);
                }
            }
            result = new_result;
        }
        result
    }

    /// Strategy that generates a type environment with 1-3 types,
    /// each having 1-3 constructors with 0-2 arguments.
    fn arb_type_env() -> impl Strategy<Value = TypeEnv> {
        // Number of types: 1 to 3
        (1..=3usize).prop_flat_map(|num_types| {
            // For each type, generate 1-3 constructors
            let type_strategies: Vec<_> = (0..num_types)
                .map(|type_idx| {
                    let num_types = num_types;
                    (1..=3usize).prop_flat_map(move |num_ctors| {
                        let ctor_strategies: Vec<_> = (0..num_ctors)
                            .map(|ctor_idx| {
                                // 0-2 arguments, each referencing a type in the env
                                proptest::collection::vec(0..num_types, 0..=2).prop_map(
                                    move |arg_type_indices| GenConstructor {
                                        name: format!("T{type_idx}C{ctor_idx}"),
                                        arg_types: arg_type_indices
                                            .into_iter()
                                            .map(TypeId)
                                            .collect(),
                                    },
                                )
                            })
                            .collect();
                        ctor_strategies
                    })
                })
                .collect();
            type_strategies
        })
        .prop_map(|types| TypeEnv { types })
    }

    proptest! {
        #[test]
        fn exhaustive_set_is_reported_exhaustive(env in arb_type_env()) {
            // Generate exhaustive patterns for the first type at depth 2
            let patterns = generate_exhaustive_patterns(&env, TypeId(0), 2);
            // Should be exhaustive
            let uncovered = check_exhaustiveness(&patterns, &env);
            prop_assert!(
                uncovered.is_empty(),
                "Expected exhaustive but got uncovered: {:?}\nPatterns: {:?}\nEnv: {:?}",
                uncovered, patterns, env
            );
        }

        #[test]
        fn removing_one_branch_breaks_exhaustiveness(
            env in arb_type_env(),
            seed in any::<usize>(),
        ) {
            let patterns = generate_exhaustive_patterns(&env, TypeId(0), 2);
            // Need at least 2 patterns to remove one and still have a meaningful test
            prop_assume!(patterns.len() >= 2);

            let remove_idx = seed % patterns.len();
            let mut reduced = patterns.clone();
            reduced.remove(remove_idx);

            let uncovered = check_exhaustiveness(&reduced, &env);
            prop_assert!(
                !uncovered.is_empty(),
                "Removed pattern at index {} ({:?}) but checker still reports exhaustive.\nAll patterns: {:?}\nEnv: {:?}",
                remove_idx, patterns[remove_idx], patterns, env
            );
        }
    }
}

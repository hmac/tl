# Plan: Deep Exhaustiveness Checking via Pattern Subtraction

## Goal

Replace the current top-level-only exhaustiveness check with a recursive algorithm that catches missing nested patterns like `Some (MkPair False n)`.

## Architecture

### New module: `src/exhaustiveness.rs`

Keep this as a standalone module with its own types. This makes it easy to unit test without needing the full typechecker. The module exports a single public function that the typechecker calls.

### Core data types

```rust
/// A "pattern" in the abstract sense used by the algorithm.
/// Not the same as ast::Pattern — this is simpler and doesn't carry locations.
enum AbstractPattern {
    /// Matches a specific constructor with sub-patterns for its arguments
    Constructor { name: GlobalName, args: Vec<AbstractPattern> },
    /// Matches anything
    Wildcard,
    /// Matches a specific integer literal
    IntLiteral(i64),
}
```

```rust
/// Information about a type needed for exhaustiveness checking:
/// what are its constructors and how many arguments does each take?
struct TypeInfo {
    constructors: Vec<(GlobalName, usize)>, // (name, arity)
}
```

### Core algorithm: `subtract`

```
fn subtract(uncovered: &AbstractPattern, branch: &AbstractPattern, type_info_fn) -> Vec<AbstractPattern>
```

Given an uncovered pattern `q` and a branch pattern `p`:

- `(Wildcard, Wildcard)` → `[]` (fully covered)
- `(Wildcard, Constructor C p1..pn)` → expand wildcard into all constructors of the type. For each constructor K:
  - If K == C: recurse on children, return residuals wrapped in C
  - If K != C: keep `K(_, _, ...)` unchanged
- `(Constructor C q1..qn, Constructor C p1..pn)` (same) → recurse on children pairwise. Fan out: for each child position i where `subtract(qi, pi)` produces residuals, emit a pattern with that residual at position i and wildcards restored at later positions.
- `(Constructor C .., Constructor D ..)` (different) → `[q]` (not covered by this branch)
- `(Constructor C .., Wildcard)` → `[]` (fully covered)
- `(IntLiteral n, IntLiteral n)` → `[]`
- `(IntLiteral n, IntLiteral m)` → `[q]`
- `(Wildcard, IntLiteral _)` → `[Wildcard]` (we can't enumerate all ints, so remain conservative)

The `type_info_fn` is a closure/trait that, given a constructor name, returns the TypeInfo for the type it belongs to. This lets us look up sibling constructors without depending on the full Typechecker.

### Conversion from `ast::Pattern` to `AbstractPattern`

A straightforward recursive conversion:
- `Pattern::Constructor { name, args, .. }` → `Constructor { name, args: convert(args) }`
- `Pattern::Var { .. }` / `Pattern::Wildcard { .. }` → `Wildcard`
- `Pattern::ListNil` → `Constructor { name: "Nil", args: [] }`
- `Pattern::ListCons { elems, tail }` → nested `Constructor { name: "Cons", args: [elem, rest] }` (desugar `[a, b, ..t]` into `Cons(a, Cons(b, t))`)
- `Pattern::Tuple { elems }` → `Constructor { name: "Tuple_N", args: convert(elems) }` (treat tuples as single-constructor types)
- `Pattern::Int { value }` → `IntLiteral(value)`

### Top-level entry point

```rust
pub fn check_exhaustiveness(
    branches: &[ast::Pattern],
    target_type: &Type,
    lookup: &dyn ConstructorLookup,
) -> Vec<AbstractPattern>  // returns the uncovered patterns (empty = exhaustive)
```

1. Convert each `ast::Pattern` to `AbstractPattern`
2. Start with `uncovered = vec![Wildcard]`
3. For each branch pattern `p`, compute new uncovered:
   `uncovered = uncovered.flat_map(|q| subtract(q, p, lookup))`
4. Return remaining uncovered patterns

### Integration with the typechecker

Replace the body of `check_case_is_exhaustive` with a call to the new module:

```rust
fn check_case_is_exhaustive(...) -> Result<(), Error> {
    let lookup = TypecheckerLookup { typechecker: self };
    let uncovered = exhaustiveness::check_exhaustiveness(patterns, target_type, &lookup);
    if uncovered.is_empty() {
        Ok(())
    } else {
        Err(Error::MissingCasePattern {
            loc,
            patterns: uncovered,  // update error to show full patterns
        })
    }
}
```

### Update `MissingCasePattern` error

Change from reporting a single constructor name to reporting the full uncovered pattern(s). Update the `Display` impl to render them readably (e.g., `Some (MkPair False _)`).

## File changes

1. **New file: `src/exhaustiveness.rs`** — the algorithm, `AbstractPattern`, conversion, and unit tests
2. **Modify: `src/typechecker.rs`** — replace `check_case_is_exhaustive` body, update `MissingCasePattern` error variant
3. **Modify: `src/lib.rs`** — add `mod exhaustiveness;`
4. **Modify: `src/ast.rs`** — update `MissingCasePattern` Display if error moves
5. **New fixtures: `fixtures/type_errors/missing_nested_pattern_*.tl`** — integration tests for the new behavior
6. **Update fixtures: `fixtures/type_errors/missing_case_pattern_1.tl`** and `lambda_case_missing_pattern.tl` — update expected output if error message format changes

## Testing strategy

### Unit tests (in `src/exhaustiveness.rs`)

These test the subtract algorithm directly, without parsing or typechecking:

1. **Wildcard vs single constructor** — `subtract(_, Some _)` on `Option` produces `[None]`
2. **Full coverage** — subtract all constructors from wildcard produces `[]`
3. **Nested patterns** — `subtract(_, Some True)` on `Option Bool` produces `[None, Some False]`
4. **Multiple branches** — full pipeline: `[Some True, None]` leaves `[Some False]`
5. **List patterns** — `[Cons(_, Wildcard), Nil]` covers all of `List`
6. **Tuple patterns** — `[(True, _)]` on `(Bool, Int)` leaves `[(False, _)]`
7. **Same constructor, different children** — `subtract(Some True, Some False)` produces `[Some True]`
8. **Wildcard branch covers everything** — `subtract(Some True, _)` produces `[]`
9. **Integer literals** — `subtract(_, 0)` stays `[_]` (can't enumerate ints)
10. **Deep nesting** — `Some (MkPair True _)` leaves `Some (MkPair False _)` and `None`

### Property tests (using `proptest` or `quickcheck`)

**Key property — removal breaks exhaustiveness**:
1. Generate a random type environment (a set of types with constructors, possibly nested)
2. Generate a set of `AbstractPattern`s that is known to be exhaustive for some type in that environment (e.g. by enumerating all leaf patterns up to some depth)
3. Remove one randomly chosen branch
4. Assert that `check_exhaustiveness` returns a non-empty uncovered set

This is the most valuable property test because it:
- Naturally produces interesting nested patterns without hand-crafting
- Directly tests the core invariant: the algorithm must notice when coverage is incomplete
- The generation strategy is straightforward: expand all constructors recursively to a bounded depth, producing a complete pattern set, then delete one

**Generation sketch**:
```rust
fn generate_exhaustive_patterns(type_info: &TypeEnv, ty: TypeId, depth: usize) -> Vec<AbstractPattern> {
    if depth == 0 {
        return vec![Wildcard];
    }
    let ctors = type_info.constructors_of(ty);
    ctors.flat_map(|(name, arg_types)| {
        // For each constructor, recursively generate exhaustive patterns for its args
        // and take the cartesian product
        let arg_pattern_sets: Vec<Vec<AbstractPattern>> = arg_types
            .iter()
            .map(|t| generate_exhaustive_patterns(type_info, t, depth - 1))
            .collect();
        cartesian_product(arg_pattern_sets)
            .map(|args| Constructor { name, args })
    }).collect()
}
```

Then pick a random index, remove it, and assert the checker catches it.

**Additional properties** (lower priority):
- **Soundness**: A full exhaustive set reports no uncovered patterns
- **Monotonicity**: Adding a branch pattern never increases the uncovered set size

### Integration tests (fixture-based)

New `.tl` fixture files that go through the full pipeline:

1. **`missing_nested_pattern_option_bool.tl`** — `case x { Some True -> ..., None -> ... }` reports `Some False`
2. **`missing_nested_pattern_pair.tl`** — `case x { (True, True) -> ... }` reports `(True, False)`, `(False, _)` etc.
3. **`nested_pattern_exhaustive.tl`** — `case x { Some True -> ..., Some False -> ..., None -> ... }` passes
4. **`missing_nested_list_pattern.tl`** — `case x { [Some n, ..r] -> ..., [] -> ... }` reports `[None, .._]`

Update existing fixtures if the error message format changes.

## Implementation order

1. Create `src/exhaustiveness.rs` with `AbstractPattern`, conversion from `ast::Pattern`, and the `subtract` algorithm
2. Write unit tests for `subtract` to validate the algorithm in isolation
3. Add the `ConstructorLookup` trait and implement it for the typechecker
4. Wire up `check_case_is_exhaustive` to call the new code
5. Update `MissingCasePattern` error to display full patterns
6. Update existing fixture expected outputs
7. Add new fixture integration tests for nested patterns
8. Run full test suite, fix any regressions

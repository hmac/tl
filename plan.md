# Plan: Add no-target-case form

## What it is

A `case` expression with no target, acting as a `cond` / multi-way conditional:

```tl
case {
  gt x 0 -> "positive",
  eq x 0 -> "zero",
  _ -> "negative"
}
```

Each branch LHS is a boolean expression (not a pattern). The first branch whose LHS evaluates to `True` is taken. A `_` wildcard branch always matches (acts as `else`).

## Desugaring strategy

Desugar in the parser (or just after parsing) into:

```tl
case True {
  _ if e1 -> r1,
  _ if e2 -> r2,
  ...
}
```

Actually, the simplest approach: **desugar directly to nested case-on-Bool**:

```tl
case e1 {
  True -> r1,
  False -> case e2 {
    True -> r2,
    False -> case e3 {
      True -> r3,
      False -> ...
    }
  }
}
```

This requires zero changes to the typechecker, compiler, or VM. The wildcard `_` branch is the final `False -> rhs` with no further nesting.

## Changes by file

### 1. `src/ast.rs`
- Make `target` in `Expr::Case` an `Option<Box<Expr>>`:
  ```rust
  Case {
      loc: Loc,
      target: Option<Box<Expr>>,
      branches: Vec<CaseBranch>,
  }
  ```
- Add a new `CaseCondBranch` struct for the no-target form (before desugaring):
  ```rust
  pub struct CaseCondBranch {
      pub loc: Loc,
      pub condition: CaseCondition, // Expr or Wildcard
      pub rhs: Expr,
  }
  ```

  Actually, **simpler**: don't change the AST at all. Desugar in the parser directly to nested `Expr::Case` with `target: Box<Expr>`. The no-target form never appears in the AST — it's pure syntactic sugar.

### 2. `src/parser.rs` — `parse_case()`

Current flow:
1. `eat("case")`
2. `parse_expr()` → target
3. `eat("{")`
4. parse branches
5. `eat("}")`

New flow:
1. `eat("case")`
2. peek next char — if `{`, this is a no-target case
3. If no-target:
   - `eat("{")`
   - Parse cond branches: each is `expr -> expr` or `_ -> expr`
   - `eat("}")`
   - Desugar into nested `Expr::Case` on Bool
4. If target present: existing behavior

New helper: `parse_cond_branch()`:
- If `_`, parse `_ -> expr` (the else branch)
- Otherwise, parse `expr -> expr`

Desugaring function: `desugar_cond_branches(loc, branches) -> Expr`:
- Takes `Vec<(Option<Expr>, Expr)>` where `None` condition = wildcard
- Builds nested `case condition { True -> rhs, False -> <recurse> }`
- The wildcard/last branch becomes the innermost `False ->` RHS
- If no wildcard: error (non-exhaustive)

### 3. `tree-sitter-tl/grammar.js`

Update the `case` rule to allow optional target:
```js
case: $ => seq(
  "case",
  optional($._expr),
  "{",
  sep_by(",", $.branch),
  "}"
),
```

Or add a separate `cond` rule. The branch rule also changes since LHS can be an expression or `_` instead of just a pattern.

### 4. No changes needed
- **`src/compiler.rs`** — only sees desugared nested `Case` with targets
- **`src/vm.rs`** — only sees normal `Case` instructions
- **`src/typechecker.rs`** — only sees nested `Case { target: Bool, branches: [True -> ..., False -> ...] }`
- **`src/ast.rs`** — no structural changes needed

### 5. Tests

Add fixtures:
- `fixtures/tests/cond.tl` — basic no-target case
- `fixtures/tests/cond_nested.tl` — nested no-target case
- `fixtures/type_errors/cond_non_bool.tl` — LHS that isn't Bool should error
- `fixtures/type_errors/cond_non_exhaustive.tl` — missing wildcard/else

### 6. Edge cases to handle

- Empty `case {}` — error (already handled by `EmptyMatch`)
- All branches are wildcards `case { _ -> 1, _ -> 2 }` — first one wins, but second is dead code
- Wildcard not in last position — could warn or error
- Single branch `case { e -> r }` — non-exhaustive without wildcard (what if `e` is False?)

## Implementation order

1. Parser: detect no-target form and parse cond branches
2. Parser: desugar cond branches to nested Case expressions
3. Tree-sitter grammar: update for syntax highlighting
4. Add test fixtures
5. Run existing tests to verify nothing breaks

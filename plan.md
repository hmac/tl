# Plan: Add no-target-case form (lambda-case)

## What it is

A `case` expression with no target — same patterns, same branches, but it produces a **function** that takes one argument and matches on it. Like Haskell's `\case`.

```tl
// before
f : Option Int -> Int { x -> case x { Some n -> n, None -> 0 } }

// after
f : Option Int -> Int { case { Some n -> n, None -> 0 } }
```

The branches use the exact same patterns as regular `case`. The only difference is the absence of a target expression.

## Desugaring strategy

Desugar in the parser to a `Func` wrapping a `Case`:

```
case { Pat1 -> e1, Pat2 -> e2 }
```
becomes:
```
\__arg -> case __arg { Pat1 -> e1, Pat2 -> e2 }
```

This requires zero changes to the typechecker, compiler, or VM. The no-target form never appears in the AST — it's pure syntactic sugar for a lambda + case.

## Changes by file

### 1. `src/parser.rs` — `parse_case()`

Current flow:
1. `eat("case")`
2. `parse_expr()` → target
3. `eat("{")`
4. parse branches
5. `eat("}")`

New flow:
1. `eat("case")`
2. `trim()`, peek next char — if `{`, this is a no-target case
3. If no-target:
   - `eat("{")`
   - Parse branches with `parse_match_branch()` (same as regular case)
   - `eat("}")`
   - Generate a fresh variable name (e.g. `__case_arg`)
   - Return `Expr::Func { args: [__case_arg], body: Expr::Case { target: __case_arg, branches } }`
4. If target present: existing behavior (unchanged)

### 2. `tree-sitter-tl/grammar.js`

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

### 3. No changes needed
- **`src/ast.rs`** — no structural changes; desugared form uses existing `Func` + `Case`
- **`src/compiler.rs`** — only sees a normal `Func` containing a `Case`
- **`src/vm.rs`** — only sees normal instructions
- **`src/typechecker.rs`** — infers the `Func` type as `a -> b` where `a` is the pattern type and `b` is the branch result type

### 4. Tests

Add fixtures:
- `fixtures/tests/lambda_case.tl` — basic no-target case used as a function body
- `fixtures/tests/lambda_case_applied.tl` — no-target case applied inline, e.g. `(case { Some n -> n, None -> 0 }) (Some 5)`

### 5. Edge cases

- Empty `case {}` — produces a function that always fails to match (existing `EmptyMatch` error at typecheck time)
- `case { ... }` used in a position where a function is expected — works naturally since it desugars to a `Func`
- Free variable name collision — use a name like `__case_arg` that users can't normally write (or a guaranteed-fresh gensym)

## Implementation order

1. Parser: detect no-target form (peek for `{` after `case`)
2. Parser: parse branches normally, wrap in `Func` + `Case`
3. Tree-sitter grammar: make target optional
4. Add test fixtures
5. Run existing tests to verify nothing breaks

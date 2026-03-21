# tl Language Design Review

## Overview

**tl** is a statically-typed, pure functional language implemented in Rust. It compiles to bytecode for a stack-based VM. The implementation is clean, well-structured, and demonstrates a solid understanding of programming language fundamentals. This review covers the language design, its strengths, and areas worth considering for future evolution.

---

## Strengths

### 1. Clean, Minimal Syntax

The language has a pleasingly small surface area. Declarations are the only top-level construct, and the syntax for functions is concise:

```
length : List a -> Int {
  l -> case l {
    [] -> 0,
    [_, ..xs] -> + 1 (length xs)
  }
}
```

The colon-separated type annotation followed by the body in braces is readable and avoids the verbosity of keyword-heavy languages. There's no `fn`, `def`, `let`, or `=` noise at the top level -- just `name : type { body }`.

### 2. Lambda-Case is a Great Feature

The `case { ... }` (no target) syntax that creates an anonymous single-argument function is elegant. It reduces boilerplate in many common patterns:

```
is_red : Tree k v -> Bool {
  case { Node Red _ _ _ _ -> True, _ -> False }
}
```

This is one of those features (inspired by Haskell's `LambdaCase` extension) that pays for itself immediately. The implementation correctly desugars it to a function wrapping a case expression in both the typechecker and compiler.

### 3. Algebraic Data Types Done Right

The ADT syntax is clean and the type system handles parameterized types well:

```
type Tree k v {
  Leaf,
  Node Colour (Tree k v) k v (Tree k v)
}
```

The red-black tree example (`fixtures/tests/red_black_tree.tl`) is a good stress test -- it exercises nested patterns, polymorphic types, higher-order functions, and recursive types all at once, and it works.

### 4. Prefix Operator Application

Using operators in prefix position (`+ 1 2`, `== x y`) is a bold but consistent choice. It means operators are just functions, which enables partial application naturally:

```
sum : List Int -> Int { foldl (+) 0 }
```

This is simpler to parse and more uniform than infix operators with precedence rules. It does trade readability for deeply nested arithmetic, but for a language centered on algebraic data and pattern matching rather than number crunching, it's a reasonable tradeoff.

### 5. Solid Type Inference

The bidirectional type checking approach works well. Top-level functions require annotations (which serves as documentation), while local expressions benefit from inference. The handling of polymorphic type variables (`VarState::Poly` preventing unification of signature-level type variables) is correct and important.

### 6. Lists as First-Class Syntax

The list syntax with cons patterns (`[x, ..xs]`) and cons expressions (`[x, ..rest]`) is intuitive and well-integrated. It avoids the need to expose `Cons`/`Nil` constructors while still allowing structural decomposition via patterns.

### 7. Built-in Test Support

Having `test` as a first-class declaration is excellent for a language at this stage. Tests are type-checked (must return `Bool`) and compiled alongside the rest of the program. This encourages testing from day one.

---

## Design Considerations and Potential Issues

### 1. No `if/then/else` -- Is That Intentional?

All conditional logic must go through `case`. While this is pure and uniform, it makes simple conditionals verbose:

```
// What you write:
case == x 0 { True -> "zero", False -> "nonzero" }

// What many languages offer:
if == x 0 then "zero" else "nonzero"
```

`if/then/else` could be trivially desugared to a `case` on `Bool`. This would improve readability without adding complexity to the type system or runtime. Worth considering as syntactic sugar.

### 2. Operators Are Very Limited

Currently there are only 7 built-in operators: `+`, `-`, `*`, `<`, `==`, `chars`, `char_at`. Notable absences:

- **No division or modulo** (`/`, `%`) -- you can't write FizzBuzz
- **No greater-than** (`>`, `>=`, `<=`) -- forces awkward workarounds
- **No string concatenation** -- strings are second-class despite being a primitive type
- **No logical operators** (`&&`, `||`, `not`) -- must be defined in userland via case expressions
- **No negation** (unary `-`)

The operator set should be expanded, or (better) the language should support user-defined operators or at least a mechanism for defining new primitive operations.

### 3. No Recursive Let Bindings

`let` bindings cannot refer to themselves or to later bindings in the same block. This means you can't define local recursive helpers:

```
// This won't work:
let go = acc l -> case l { [] -> acc, [x, ..xs] -> go (+ acc x) xs }
{ go 0 myList }
```

You're forced to define a top-level helper function instead, which clutters the module namespace. Supporting `let rec` (or making all `let` bindings recursive by default, like Haskell's `where`) would be a significant ergonomic improvement.

### 4. No String Interpolation or Operations

Strings (`Str`) are a primitive type, but there are almost no operations on them beyond `chars` (convert to char list) and `char_at`. There's no way to:

- Concatenate strings
- Convert integers to strings (for output/debugging)
- Compare strings (beyond structural equality)
- Get string length

This makes the language impractical for anything involving text processing or user-facing output.

### 5. Exhaustiveness Checking is Shallow

The exhaustiveness checker (`check_case_is_exhaustive`) only checks top-level patterns. It correctly notes this limitation in a comment referencing the "Lower Your Guards" paper. In practice, this means:

```
type Option a { Some a, None }

// This will NOT warn about the missing `None` case if nested:
case pair {
  (Some x, True) -> x,
  // missing: (None, _), (_, False)
}
```

The current approach is fine for now, but as programs grow more complex, deep exhaustiveness checking becomes important for safety.

### 6. Infer Returns Wrong Type for `Char` Literals

In `typechecker.rs:933`:
```rust
Expr::Char(_, _) => Ok(TYPE_STRING),  // Bug: should be TYPE_CHAR
```

`infer_expr` for `Char` literals returns `Type::Str` instead of `Type::Char`. The `check_expr` path is correct (line 530), so this only manifests when a char literal's type needs to be *inferred* rather than checked. This is a bug.

### 7. No Module Visibility Control

Everything defined in a module is automatically exported. There's no `pub`/`private` distinction. As programs grow, this leads to namespace pollution and makes it hard to maintain internal invariants (e.g., the red-black tree's balancing functions shouldn't be part of its public API).

### 8. Constructor Names Must Be Globally Unique

From the error message: *"constructor names must be globally unique"*. This is a significant restriction. You can't define `None` in two different files, even if they define different types. This will cause problems as programs grow. Most languages scope constructors to their type or module.

### 9. Tuple Syntax Has a Trailing Comma Requirement

Tuples require a trailing comma for single-element tuples and the syntax `(,)` for the unit/empty tuple. The type `(a, b,)` with trailing comma is unusual and could confuse users coming from other languages. Consider whether `()` for unit and `(a, b)` for pairs (with no trailing comma) would be cleaner.

### 10. No Error Recovery in the Parser

The parser is recursive descent with no error recovery. The first parse error aborts the entire compilation. For a production language, recovering from errors (to report multiple issues at once) would improve the developer experience.

### 11. Tail Call Optimization is Limited

TCO is only applied for direct self-recursion (`TailCall` instruction). Mutual recursion, continuation-passing style, and tail calls to other functions are not optimized. Since the language has no loops, stack overflow on large inputs is a real concern. The `permutations` test is disabled because it's slow -- likely related to deep recursion without optimization.

### 12. No Integer Overflow Handling

Integers are `i64` with no overflow detection. Arithmetic silently wraps. For a language that aims for safety through types, this is a gap. Consider at least panicking on overflow (like Rust's debug mode) or supporting arbitrary-precision integers.

---

## Architecture Notes

### Compiler Pipeline

The pipeline `Source -> Parser -> AST -> Typechecker -> Compiler -> VM` is clean and well-separated. Each phase has a single responsibility. The `Runner` in `lib.rs` orchestrates the phases well, with proper error reporting at each stage.

### The VM Design

The stack-based VM is straightforward. The use of `StackValue` (an enum with inline `Int`/`Bool`/`Char` variants plus a heap-allocated `HeapValue` for complex types) is a good optimization that avoids heap allocation for common primitives.

The `Thunk` mechanism for lazy evaluation of globals is interesting but could be documented more -- it's not obvious from the language semantics that evaluation is lazy.

### Lambda Lifting

The compiler's lambda lifting approach is correct but produces closures that capture *all* locals in scope, not just free variables. The `Expr::free_variables()` method exists in the AST but isn't used during compilation. Using it would reduce closure sizes and improve performance.

---

## Summary

**tl** is a well-designed teaching/hobby language that makes good choices in its core design: algebraic data types, pattern matching, polymorphic type inference, and a clean syntax. The implementation is solid -- the red-black tree and permutations examples demonstrate real expressive power.

The main areas for improvement are:

1. **Expand the primitive operator set** (division, modulo, string operations, comparison operators)
2. **Fix the `Char` inference bug** (returns `Str` instead of `Char`)
3. **Add recursive `let` bindings** (major ergonomic win)
4. **Consider `if/then/else` sugar** (readability improvement for boolean branching)
5. **Relax the global constructor uniqueness constraint** (will be necessary for larger programs)
6. **Use free variable analysis in lambda lifting** (the code for it already exists)

The language is at a good point where these incremental improvements would significantly expand what users can practically build with it.

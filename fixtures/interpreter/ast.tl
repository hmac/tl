// TODO
type String {}

type Expr {
  Var Var,
  Integer Int,
  Match Expr (List Branch),
  Func (List String) Expr,
  App Expr Expr
}

type Branch {
  Branch Pattern Expr
}

type Pattern {
  CtorPat String (List Pattern),
  VarPat String,
  IntPat Int,
  WildPat
}

type Var {
  LocalVar String,
  CtorVar String,
  OpVar Operator
}

type Operator { Add, Sub, Mul }

main : Int { 4 }
---
4

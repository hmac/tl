type Bool { True, False }

iszero : Int -> Bool {
  n -> match n {
    0 -> True,
    _ -> False
  }
}

sum : Int -> Int -> Int {
  // currently match targets must be variables, not expressions.
  // without let expressions or expressions in matches, we can't express much.
  n acc -> match iszero n {
    True -> acc,
    False -> sum (- n 1) (+ acc n)
  }
}

main : Bool { sum 6 0 }
---
False

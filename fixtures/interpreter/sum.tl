iszero : Int -> Bool {
  n -> case n {
    0 -> True,
    _ -> False
  }
}

sum : Int -> Int -> Int {
  n acc -> case iszero n {
    True -> acc,
    False -> sum (- n 1) (+ acc n)
  }
}

main : Int { sum 6 0 }
---
21

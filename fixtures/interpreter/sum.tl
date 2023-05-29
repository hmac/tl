iszero : Int -> Bool {
  n -> match n {
    0 -> True,
    _ -> False
  }
}

sum : Int -> Int -> Int {
  n acc -> match iszero n {
    True -> acc,
    False -> sum (- n 1) (+ acc n)
  }
}

main : Int { sum 6 0 }
---
21

type Bool { True, False }

iszero : Int -> Bool {
  n -> match n {
    0 -> True,
    1 -> False,
    4 -> False
  }
}

main : Bool { iszero 4 }
---
False

type Bool { True, False }

not : Bool -> Bool {
  b -> match b {
    True -> False,
    False -> True
  }
}

main : Bool { not False }
---
True

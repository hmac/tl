not : Bool -> Bool {
  b -> case b {
    True -> False,
    False -> True
  }
}

main : Bool { not False }
---
True

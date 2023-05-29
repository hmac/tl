// Test that Bool is recognised as a builtin type

not : Bool -> Bool {
  b -> match b {
    True -> False,
    False -> True
  }
}

main : Bool { not False }
---
True

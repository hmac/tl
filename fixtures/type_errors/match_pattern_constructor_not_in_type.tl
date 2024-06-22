type Dir { Left, Right }

foo : Bool -> Bool {
  b -> case b {
    // This constructor does not have the same type as the target
    Left -> True,
    False -> False,
    True -> True,
  }
}
---
Error:

fixtures/type_errors/match_pattern_constructor_not_in_type.tl:
   5:     // This constructor does not have the same type as the target
   6:     Left -> True,
          ^^^^^
           expected this to have the type Bool but it actually has the type Dir

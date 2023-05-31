type Dir { Left, Right }

foo : Bool -> Bool {
  b -> case b {
    // This constructor does not have the same type as the target
    Left -> True,
    False -> False
  }
}
---
Error:

   5:     // This constructor does not have the same type as the target
   6:     Left -> True,
          ^^^^^
           expected this to have the type Bool, but it actually has the type Dir

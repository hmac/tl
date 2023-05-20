type Bool { True, False }

type Dir { Left, Right }

foo : Bool -> Bool {
  b -> match b {
    // This constructor does not have the same type as the target
    Left -> True,
    False -> False
  }
}
---
Error:

   7:     // This constructor does not have the same type as the target
   8:     Left -> True,
          ^^^^^
           expected this to have the type Bool, but it actually has the type Dir

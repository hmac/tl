f : (Int, (Int, Bool)) -> Int {
  x -> 1
}

g : Int { f (6, False) }
---
Error:

   4:
   5: g : Int { f (6, False) }
                      ^^^^^
                       expected this to have the type (Int, Bool) but it actually has the type Bool

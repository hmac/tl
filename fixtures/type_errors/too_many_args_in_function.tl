f : Int -> Int { x y z -> 1 }

main : Int { f 1 2 3 }
---
Error:

   1: f : Int -> Int { x y z -> 1 }
                             ^^^^^
                              this function takes 3 arguments, but its type (Int -> Int) has only 2 arguments


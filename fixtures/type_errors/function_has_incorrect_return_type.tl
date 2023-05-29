f : Int -> Int {
  x -> True
}
---
Error:

   1: f : Int -> Int {
   2:   x -> True
             ^^^^
              expected this to have the type Int, but it actually has the type Bool

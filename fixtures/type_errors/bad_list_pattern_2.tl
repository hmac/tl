// x is a List Int, but we are matching it with a List Bool pattern
f : List Int -> Int {
  x -> case x {
    [True] -> 0,
  }
}
---
Error:

   3:   x -> case x {
   4:     [True] -> 0,
           ^^^^
            expected this to have the type Int, but it actually has the type Bool

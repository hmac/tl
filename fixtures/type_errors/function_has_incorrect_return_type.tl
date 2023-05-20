type Bool { True, False }

f : Int -> Int {
  x -> True
}
---
Error:

   3: f : Int -> Int {
   4:   x -> True
             ^^^^
              expected this to have the type Int, but it actually has the type Bool

// the pattern has mismatching element types (Int and Bool)
f : List Bool -> Int {
  x -> case x {
    [True, 1] -> 0,
  }
}
---
Error:

   3:   x -> case x {
   4:     [True, 1] -> 0,
                 ^
                  expected this to have the type Bool but it actually has the type Int

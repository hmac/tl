// the pattern has mismatching element and tail types (Int and List Int)
f : List Int -> Int {
  x -> case x {
    [1, ..[[2]]] -> 0,
  }
}

main : Int { f [1] }
---
Error:

   3:   x -> case x {
   4:     [1, ..[[2]]] -> 0,
                 ^^^
                  expected this to have the type Int, but it actually has the type List a2

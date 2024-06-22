// the pattern has mismatching element and tail types (Int and List Int)
f : List Int -> Int {
  x -> case x {
    [1, ..[[2]]] -> 0,
    [] -> 1
  }
}

main : Int { f [1] }
---
Error:

fixtures/type_errors/bad_list_element_5.tl:
   3:   x -> case x {
   4:     [1, ..[[2]]] -> 0,
                 ^^^
                  expected this to have the type Int but it actually has the type List a2

// the pattern has mismatching element types (List Int and List (List Int))
f : List (List Int) -> Int {
  x -> case x {
    [[1], [[2]]] -> 0,
  }
}
---
Error:

fixtures/type_errors/bad_list_element_4.tl:
   3:   x -> case x {
   4:     [[1], [[2]]] -> 0,
                 ^^^
                  expected this to have the type Int but it actually has the type List a3

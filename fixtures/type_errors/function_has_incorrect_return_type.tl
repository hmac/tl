f : Int -> Int {
  x -> True
}
---
Error:

fixtures/type_errors/function_has_incorrect_return_type.tl:
   1: f : Int -> Int {
   2:   x -> True
             ^^^^
              expected this to have the type Int but it actually has the type Bool

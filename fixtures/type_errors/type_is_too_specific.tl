// This function's type is a -> a but it actually has type a -> Bool.
// This is too specific.
main : a -> a {
  _ -> True
}
---
Error:

fixtures/type_errors/type_is_too_specific.tl:
   3: main : a -> a {
   4:   _ -> True
             ^^^^
              expected this to have the type a but it actually has the type Bool

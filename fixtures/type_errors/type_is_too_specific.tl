// This function's type is a -> a but it actually has type a -> Bool.
// This is too specific.
type Bool { True, False }

main : a -> a {
  _ -> True
}
---
Error:

   5: main : a -> a {
   6:   _ -> True
             ^^^^
              expected this to have the type a, but it actually has the type Bool

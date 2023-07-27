// This function takes two arguments but its type takes three.
main : (a -> b) -> b -> c -> c {
  f x -> x
}
---
Error:

   2: main : (a -> b) -> b -> c -> c {
   3:   f x -> x
               ^
                expected this to have the type c -> c but it actually has the type b

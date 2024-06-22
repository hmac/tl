// This function takes two arguments but its type takes three.
main : (a -> b) -> b -> c -> c {
  f x -> x
}
---
Error:

fixtures/type_errors/too_few_arguments.tl:
   2: main : (a -> b) -> b -> c -> c {
   3:   f x -> x
               ^
                expected this to have the type c -> c but it actually has the type b

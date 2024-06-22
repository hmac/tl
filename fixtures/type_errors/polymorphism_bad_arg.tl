apply : (a -> b) -> a -> b {
  f x -> f x
}

main : Int {
  apply (x -> + x 1) True
}
---
Error:

fixtures/type_errors/polymorphism_bad_arg.tl:
   5: main : Int {
   6:   apply (x -> + x 1) True
                           ^^^^
                            expected this to have the type Int but it actually has the type Bool


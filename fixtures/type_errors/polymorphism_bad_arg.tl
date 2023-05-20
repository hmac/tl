apply : (a -> b) -> a -> b {
  f x -> f x
}

type Bool { True, False }

main : Int {
  apply (x -> + x 1) True
}
---
Error:

   7: main : Int {
   8:   apply (x -> + x 1) True
                           ^^^^
                            expected this to have the type Int, but it actually has the type Bool


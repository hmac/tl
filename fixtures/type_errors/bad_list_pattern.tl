// x is an Int, but we are matching it with a list pattern
f : Int -> Int {
  x -> case x {
    [] -> 0
  }
}
---
Error:

   3:   x -> case x {
   4:     [] -> 0
          ^^
           expected this to have the type Int but it actually has the type List a

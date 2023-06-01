main : List Int {
  let x = [1] {
    [1, 2, x]
  }
}
---
Error:

   2:   let x = [1] {
   3:     [1, 2, x]
                 ^
                  expected this to have the type Int, but it actually has the type List Int

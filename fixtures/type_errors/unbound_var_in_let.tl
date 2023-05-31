main : Int {
  let y = x, x = 1 { y }
}
---
Error:

   1: main : Int {
   2:   let y = x, x = 1 { y }
                ^
                 unknown variable 'x'

main : Int {
  let y = x, x = 1 { y }
}
---
Error:

fixtures/type_errors/unbound_var_in_let.tl:
   1: main : Int {
   2:   let y = x, x = 1 { y }
                ^
                 unknown variable 'x'

main : List Int {
  let x = [1] {
    [1, 2, x]
  }
}
---
Error:

fixtures/type_errors/bad_list_element.tl:
   2:   let x = [1] {
   3:     [1, 2, x]
                 ^
                  expected this to have the type Int but it actually has the type List Int

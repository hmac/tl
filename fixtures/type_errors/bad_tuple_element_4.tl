f : (Int, (Int, Bool)) -> Int {
  x -> 1
}

g : Int { f (6, False) }
---
Error:

fixtures/type_errors/bad_tuple_element_4.tl:
   4: 
   5: g : Int { f (6, False) }
                      ^^^^^
                       expected this to have the type (Int, Bool) but it actually has the type Bool

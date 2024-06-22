id : a -> a { x -> x }

f : Int { id (True, False) }

---
Error:

fixtures/type_errors/bad_tuple_element_5.tl:
   2: 
   3: f : Int { id (True, False) }
                ^^
                 expected this to have the type (a1, a2) but it actually has the type Int

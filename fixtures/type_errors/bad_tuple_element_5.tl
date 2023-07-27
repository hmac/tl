id : a -> a { x -> x }

f : Int { id (True, False) }

---
Error:

   2:
   3: f : Int { id (True, False) }
                ^^
                 expected this to have the type (a1, a2) but it actually has the type Int

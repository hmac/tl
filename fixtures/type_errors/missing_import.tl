foo : Int -> Int { x -> bar.some_func 1 }
---
Error:

fixtures/type_errors/missing_import.tl:
   1: foo : Int -> Int { x -> bar.some_func 1 }
                              ^^^^^^^^^^^^^
                               this file does not import bar

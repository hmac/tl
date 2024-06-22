type A { B, B }
---
Error:

fixtures/type_errors/duplicate_constructor_in_type_decl.tl:
   1: type A { B, B }
                  ^^
                   this constructor conflicts with an existing constructor of the same name - constructor names must be globally unique

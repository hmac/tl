type Foo { MkFoo a }

main : Int { 4 }
---
Error:

fixtures/type_errors/unknown_variable_in_type.tl:
   1: type Foo { MkFoo a }
                 ^^^^^^^^
                  unknown variable 'a'

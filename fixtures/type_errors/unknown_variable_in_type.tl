type Foo { MkFoo a }

main : Int { 4 }
---
Error:

   1: type Foo { MkFoo a }
                 ^^^^^^^^
                  unknown variable 'a'

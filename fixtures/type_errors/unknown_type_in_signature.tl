foo : Nope -> Nope { n -> n }

main : Int { 4 }
---
Error:

   1: foo : Nope -> Nope { n -> n }
                 ^^
                  unknown type 'Nope'

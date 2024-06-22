foo : Nope -> Nope { n -> n }

main : Int { 4 }
---
Error:

fixtures/type_errors/unknown_type_in_signature.tl:
   1: foo : Nope -> Nope { n -> n }
                 ^^
                  unknown type 'Nope'

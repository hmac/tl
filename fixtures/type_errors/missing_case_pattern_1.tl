f : Bool -> Bool {
  x -> case x {
    True -> False
  }
}

main : Bool { f False }
---
Error:

fixtures/type_errors/missing_case_pattern_1.tl:
   1: f : Bool -> Bool {
   2:   x -> case x {
             ^
              the constructor False is not covered by this case expression

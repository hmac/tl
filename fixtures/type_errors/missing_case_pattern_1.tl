f : Bool -> Bool {
  x -> case x {
    True -> False
  }
}

main : Bool { f False }
---
Error:

   1: f : Bool -> Bool {
   2:   x -> case x {
             ^
              the constructor False is not covered by this case expression

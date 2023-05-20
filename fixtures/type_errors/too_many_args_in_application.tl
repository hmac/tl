foo : Int -> Int { x -> x }

bar : Int { foo 2 3 }
---
Error:

   2: 
   3: bar : Int { foo 2 3 }
                  ^^^
                   this function takes 1 argument, but is given 2

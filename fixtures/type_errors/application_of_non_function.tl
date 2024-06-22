foo : Int {
  1
}

bar : Int { foo 2 }
---
Error:

fixtures/type_errors/application_of_non_function.tl:
   4: 
   5: bar : Int { foo 2 }
                  ^^^
                   this expression cannot be applied as a function, because it has type Int

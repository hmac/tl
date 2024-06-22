// Ideally this would have an error which tells you there's too many arguments,
// e.g.
// Error:
// 
//    11: 
//    12: bar : Int { foo 2 3 }
//                    ^^^
//                     this function takes 1 argument, but is given 2

foo : Int -> Int { x -> x }

bar : Int { foo 2 3 }
---
Error:

fixtures/type_errors/too_many_args_in_application.tl:
  11: 
  12: bar : Int { foo 2 3 }
                  ^^^^^
                   expected this to have the type Int -> Int but it actually has the type Int

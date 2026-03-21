// lambda-case used where a non-function type is expected
main : Int { case { _ -> 0 } }
---
Error:

fixtures/type_errors/lambda_case_not_a_function.tl:
   1: // lambda-case used where a non-function type is expected
   2: main : Int { case { _ -> 0 } }
                   ^^^^^^^^^^^^^^^^
                    expected to have a function type, but its actual type is Int
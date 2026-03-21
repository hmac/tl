// empty lambda-case
main : a -> Int { case {} }
---
Error:

fixtures/type_errors/lambda_case_empty.tl:
   1: // empty lambda-case
   2: main : a -> Int { case {} }
                        ^^^^^^^^
                         match expressions cannot be empty
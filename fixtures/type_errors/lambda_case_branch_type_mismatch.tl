// lambda-case branches return different types
main : Bool -> Int {
  case {
    True -> 1,
    False -> True
  }
}
---
Error:

fixtures/type_errors/lambda_case_branch_type_mismatch.tl:
   4:     True -> 1,
   5:     False -> True
                   ^
                    expected this to have the type Int but it actually has the type Bool
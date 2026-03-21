// lambda-case branch returns the wrong type
type Option a { Some a, None }

main : Option Int -> Int {
  case {
    Some n -> True,
    None -> 0
  }
}
---
Error:

fixtures/type_errors/lambda_case_wrong_return_type.tl:
   5:   case {
   6:     Some n -> True,
                    ^^^^
                     expected this to have the type Int but it actually has the type Bool
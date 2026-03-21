// lambda-case with a missing pattern
// the error should point at the case keyword, same as regular case
type Option a { Some a, None }

main : Option Int -> Int {
  case {
    Some n -> n
  }
}
---
Error:

fixtures/type_errors/lambda_case_missing_pattern.tl:
   5: main : Option Int -> Int {
   6:   case {
        ^
         the constructor None is not covered by this case expression
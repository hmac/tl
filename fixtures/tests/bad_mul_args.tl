
type Option a {
 Some a,
 None
}

make_two_digit_number : Option Int -> Option Int -> Option Int {
 a b -> case a {
  Some a -> case b {
   Some b -> Some (+ b (* a 10)),
   None -> None
  },
  None -> None
 }
}

// test make_two_digit_number {
//  == (Some 45) (make_two_digit_number (Some 4) (Some 5))
// }

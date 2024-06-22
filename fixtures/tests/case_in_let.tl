// A case expression inside a let requires that after evaluating a case branch
// we correctly return control to the let.

f : Int {
  let x = case 1 {
    1 -> 2,
    _ -> 0,
  } {
    x
  }
}

test f {
  == f 2
}

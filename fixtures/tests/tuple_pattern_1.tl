swap : (a, b) -> (b, a) {
  case {
    (x, y) -> (y, x)
  }
}

first2 : (a, b) -> a {
  case { (x, _) -> x }
}

second2 : (a, b) -> b { case { (_, x) -> x } }

test first2 { == 1 (first2 (1, 2)) }
test second2 { == 2 (second2 (1, 2)) }
test swap2 { == (1, 2) (swap (2, 1)) }
test same { == (1, 2) (1, 2) }

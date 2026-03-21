unit : (,) { (,) }

single : (Int,) { (1,) }

pair : (Int, Bool) { (1, True) }

triple : (Int, Bool, Char) { (1, True, 'a') }

quad : (Int, Bool, Char, String) { (1, True, 'a', "hi") }

nested : (Int, (Bool, ((Char,), Bool))) -> Char {
  case {
    (i, (b, ((c,), b2))) -> c
  }
}

test nested {
  == 'A' (nested (1, (True, (('A',), False))))
}

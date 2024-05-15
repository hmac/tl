type Option a { Some a, None }

f : Option (Int, Char) {
  Some (1, 'a')
}

g : Char {
  case f {
    Some t -> case t {
      (n, c) -> c
    },
    None -> 'b'
  }
}

test g {
  == g 'a'
}

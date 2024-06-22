snd : (a, b) -> b {
  t -> case t { (x, y) -> y }
}

fst : (a, b) -> a {
  t -> case t { (x, y) -> x }
}

mapFst : (a -> b) -> (a, c) -> (b, c) {
  f t -> case t { (x, y) -> (f x, y) }
}

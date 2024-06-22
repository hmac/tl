uncurry: (a -> b -> c) -> (a, b) -> c {
  f t -> case t {
    (x, y) -> f x y
  }
}

// Polymorphism
// Not yet supported.

apply : (a -> b) -> a -> b {
  f x -> f x
}

apply2 : (a -> a) -> a -> a {
  f x -> f (f x)
}

type List a {
  Nil,
  Cons a (List a)
}

empty : List a -> Bool {
  list -> match list {
    Nil -> True,
    Cons x xs -> False
  }
}

not_empty : List a -> Bool {
  list -> not (empty list)
}

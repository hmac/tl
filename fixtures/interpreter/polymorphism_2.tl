not : Bool -> Bool {
  b -> case b {
    True -> False,
    False -> True,
  }
}

type List a {
  Nil,
  Cons a (List a)
}

empty : List a -> Bool {
  list -> case list {
    Nil -> True,
    Cons x xs -> False
  }
}

not_empty : List a -> Bool {
  list -> not (empty list)
}

main : Bool { empty Nil }
---
True

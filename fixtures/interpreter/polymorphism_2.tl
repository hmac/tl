type Bool { True, False }

not : Bool -> Bool {
  b -> match b {
    True -> False,
    False -> True,
  }
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

main : Bool { empty Nil }
---
True

type List a { Nil, Cons a (List a) }

reverse : List a -> List a {
  l -> reverse_ l Nil
}

reverse_ : List a -> List a -> List a {
  l acc -> case l {
    Nil -> acc,
    Cons x xs -> reverse_ xs (Cons x acc)
  }
}

main : List Int { reverse (Cons 3 (Cons 2 (Cons 1 Nil))) }

test reverse {
  ==
    (reverse (Cons 3 (Cons 2 (Cons 1 Nil))))
    (Cons 1 (Cons 2 (Cons 3 Nil)))
}

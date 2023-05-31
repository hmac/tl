type List a { Nil, Cons a (List a) }

map : (a -> b) -> List a -> List b {
  f l -> case l {
    Nil -> Nil,
    Cons x xs -> Cons (f x) (map f xs),
  }
}

test map {
  == (map (x -> + x 1) (Cons 1 (Cons 2 (Cons 3 Nil))))
    (Cons 2 (Cons 3 (Cons 4 Nil)))
}

foldl : (b -> a -> b) -> b -> List a -> b {
  f z l -> case l {
    Nil -> z,
    Cons x xs -> f (foldl f z xs) x
  }
}

test foldl {
  == (foldl (x y -> * x y) 1 (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil)))))
    24
}

filter : (a -> Bool) -> List a -> List a {
  p l -> foldl (acc x -> case p x { True -> Cons x acc, False -> acc }) Nil l
}

test filter {
  == (filter (x -> == x 3) (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil)))))
    (Cons 3 Nil)
}

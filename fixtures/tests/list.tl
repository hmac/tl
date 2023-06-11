map : (a -> b) -> List a -> List b {
  f l -> case l {
    Nil -> Nil,
    Cons x xs -> [f x, ..map f xs],
  }
}

test map {
  == (map (x -> + x 1) [1, 2, 3])
    [2, 3, 4]
}

foldl : (b -> a -> b) -> b -> List a -> b {
  f z l -> case l {
    Nil -> z,
    Cons x xs -> f (foldl f z xs) x
  }
}

test foldl {
  == (foldl (x y -> * x y) 1 [1, 2, 3, 4]) 24
}

filter : (a -> Bool) -> List a -> List a {
  p l -> foldl (acc x -> case p x { True -> Cons x acc, False -> acc }) Nil l
}

test filter {
  == (filter (x -> == x 3) [1, 2, 3, 4]) [3]
}

zip_with : (a -> b -> c) -> List a -> List b -> List c {
  f ls rs -> case ls {
    Nil -> Nil,
    Cons x xs -> case rs {
      Nil -> Nil,
      Cons y ys -> [f x y, ..zip_with f xs ys]
    }
  }
}

test zip_with {
  == (zip_with (x y -> + x y) [1, 2, 3] [4, 5, 6]) [5, 7, 9]
}

type Pair a b { Pair a b }

zip : List a -> List b -> List (Pair a b) {
  ls rs -> zip_with (x y -> Pair x y) ls rs
}

test zip {
  == (zip [1, 2, 3] [4, 5, 6]) [Pair 1 4, Pair 2 5, Pair 3 6]
}

len : List a -> Int { len_helper 0 }

len_helper : Int -> List a -> Int {
  acc l -> case l {
    Nil -> acc,
    Cons _ rest -> len_helper (+ acc 1) rest
  }
}

test len {
  == (len [1, 2, 3]) 3
}

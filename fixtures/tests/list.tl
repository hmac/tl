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
    Cons x xs -> foldl f (f z x) xs
  }
}

test foldl {
  == (foldl (x y -> * x y) 1 [1, 2, 3, 4]) 24
}

test foldl_empty { == (foldl (a x -> + a x) 0 []) 0 }

test foldl_list { == (foldl (a x -> [x, ..a]) [] [1, 2, 3]) [3, 2, 1] }

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

append : List a -> List a -> List a {
  ls rs -> case ls {
    Nil -> rs,
    Cons x xs -> Cons x (append xs rs)
  }
}

test append {
  == (append [1, 2, 3] [4, 5, 6]) [1, 2, 3, 4, 5, 6]
}

type Option a { None, Some a }

first : List a -> Option a {
  l -> case l {
    Nil -> None,
    Cons x _ -> Some x,
  }
}

test first { == (first [1, 2]) (Some 1) }
test first_empty { == (first Nil) None }

last : List a -> Option a {
  l -> case l {
    Nil -> None,
    Cons x Nil -> Some x,
    Cons _ r -> last r,
  }
}

test last { == (last [1, 2]) (Some 2) }
test last_one { == (last [1]) (Some 1) }
test last_empty { == (last Nil) None }

tail : List a -> Option (List a) {
  l -> case l {
    Nil -> None,
    Cons x rest -> Some rest,
  }
}

test tail { == (tail [1, 2, 3]) (Some [2, 3]) }
test tail_empty { == (tail Nil) None }

init : List a -> Option (List a) {
  l -> case l {
    Nil -> None,
    Cons x xs -> Some (init_helper x xs)
  }
}

init_helper : a -> List a -> List a {
  x l -> case l {
    Nil -> [],
    Cons y ys -> [x, ..init_helper y ys]
  }
}

test init { == (init [1, 2, 3]) (Some [1, 2]) }
test init_empty { == (init []) None }
test init_single { == (init [1]) (Some []) }

single : a -> List a {
  x -> [x]
}

test single { == (single 1) [1] }

empty : List a -> Bool {
  l -> case l { Nil -> True, Cons _ _ -> False }
}

test empty_empty { == (empty []) True }
test empty_nonempty { == (empty [1]) False }

reverse : List a -> List a {
  l -> reverse_helper l []
}

reverse_helper : List a -> List a -> List a {
  l r -> case l {
    Nil -> r,
    Cons x xs -> reverse_helper xs (Cons x r)
  }
}

test reverse { == (reverse [1, 2, 3]) [3, 2, 1] }
test reverse_empty { == (reverse []) [] }

intersperse : a -> List a -> List a {
  sep l -> case l {
    Nil -> [],
    Cons x Nil -> [x]
    Cons x xs -> [x, sep, ..intersperse sep xs]
  }
}

test intersperse {
  == (intersperse 9 [1, 2, 3]) [1, 9, 2, 9, 3]
}

unzip : List (Pair a b) -> Pair (List a) (List b) {
  let f : Pair a b -> Pair (List a) (List b) -> Pair (List a) (List b) =
    ab asbs -> case ab {
      Pair a b -> case asbs {
        Pair as bs -> Pair [a, ..as] [b, ..bs]
      }
    }
  { foldr f (Pair [] []) }
}


test_unzip_single { == (unzip [Pair 1 2]) (Pair [1] [2]) }
test_unzip { == (unzip [Pair 1 2, Pair 3 4]) (Pair [1, 3] [2, 4]) }

foldr : (a -> b -> b) -> b -> List a -> b {
  f z l -> case l {
    Nil -> z,
    Cons x xs -> f x (foldr f z xs)
  }
}

test foldr_list { == (foldr (x a -> [x, ..a]) [] [1, 2, 3]) [1, 2, 3] }

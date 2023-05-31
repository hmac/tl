type List a {
  Nil,
  Cons a (List a)
}

length : List a -> Int {
  l -> case l {
    Nil -> 0,
    Cons _ l -> + 1 (length l)
  }
}

map : (a -> b) -> List a -> List b {
  f l -> case l {
    Nil -> Nil,
    Cons x xs -> Cons (f x) (map f xs)
  }
}

fold : (a -> b -> b) -> b -> List a -> b {
  f z l -> case l {
    Nil -> z,
    Cons x xs -> f x (fold f z xs)
  }
}

// fold1 (+) [1, 2, 3] == (+ 

length2 : List a -> Int {
  l -> fold (_ acc -> + acc 1) 0 l
}

zip : List a -> List b -> List (Pair a b) {
  l r -> case l {
    Nil -> Nil,
    Cons lx lxx -> case r {
      Nil -> Nil,
      Cons rx rxx -> Cons (Pair lx rx) (zip lxx rxx)
    }
  }
}

type NonEmptyList a {
  NonEmptyList a (List a)
}

fold_ne : (a -> b -> b) -> b -> NonEmptyList a -> b {
  f z l -> case l {
    NonEmptyList x xs -> f x (fold f z xs)
  }
}

fold1 : (a -> a -> a) -> NonEmptyList a -> a {
  f l -> case l {
    NonEmptyList x xs -> fold f x xs
  }
}

non_empty_list : a -> List a -> NonEmptyList a {
  x l -> NonEmptyList x l
}

all : (a -> Bool) -> NonEmptyList a -> Bool {
  p l -> fold_ne (a b -> and (p a) b) True l
}

and : Bool -> Bool -> Bool {
  x y -> case x {
    True -> y,
    False -> False
  }
}

type Pair a b { Pair a b }

type Maybe a { None, Some a }

head : List a -> Maybe a {
  l -> case l {
    Nil -> None,
    Cons x _ -> Some x
  }
}

elimPair : (a -> b -> c) -> Pair a b -> c {
  f pair -> case pair {
    Pair x y -> f x y
  }
}

main : Int {
 case (head (zip (Cons 1 (Cons 2 Nil)) (Cons 3 (Cons 4 Nil)))) {
   None -> 0,
   Some p -> elimPair (x y -> + x y) p
 }
}
---
4

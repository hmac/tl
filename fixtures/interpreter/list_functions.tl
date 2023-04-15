type List {
  Nil,
  Cons Int List
}

length : List -> Int {
  l -> match l {
    Nil -> 0,
    Cons _ l -> + 1 (length l)
  }
}

map : (Int -> Int) -> List -> List {
  f l -> match l {
    Nil -> Nil,
    Cons x xs -> Cons (f x) (map f xs)
  }
}

fold : (Int -> Int -> Int) -> Int -> List -> Int {
  f z l -> match l {
    Nil -> z,
    Cons x xs -> f x (fold f z xs)
  }
}

lengthtwo : List -> Int {
  l -> fold (_ acc -> + acc 1) 0 l
}

type ListPair {
  NilPair,
  ConsPair Int Int ListPair
}

zip : List -> List -> ListPair {
  l r -> match l {
    Nil -> NilPair,
    Cons lx lxx -> match r {
      Nil -> NilPair,
      Cons rx rxx -> ConsPair lx rx (zip lxx rxx)
    }
  }
}

type Pair { Pair Int Int }

type MaybePair { NoPair, SomePair Pair }

headpair : ListPair -> MaybePair {
  l -> match l {
    NilPair -> NoPair,
    ConsPair x y _ -> SomePair (Pair x y)
  }
}

elimpair : (Int -> Int -> Int) -> Pair -> Int {
  f pair -> match pair {
    Pair x y -> f x y
  }
}

main : Int {
 match (headpair (zip (Cons 1 (Cons 2 Nil)) (Cons 3 (Cons 4 Nil)))) {
   NoPair -> 0,
   SomePair p -> elimpair (x y -> + x y) p
 }
}
---
4

// Basic types and functions

type Pair a { MkPair a a }

f : Int -> Int -> Int { x y -> + x y }

g : Int -> Int -> Int { x y -> - (*  x y) x }

main : Pair Bool {
  // comment inside function
  MkPair True (not True)
}

not : Bool -> Bool {
  b -> case b {
    True -> False, // comment at end of line
    False -> True
  }
}

constint : Int -> Int -> Int {
  x y -> x
}

type Unit { Unit }

id : a -> a {
  x -> x
}

andpair : Pair Bool -> Bool {
  p -> case p {
    MkPair a b -> and a b
  }
}

and : Bool -> Bool -> Bool {
  a b -> case a {
    True -> case b {
      True -> True,
      False -> False
    },
    False -> False
  }
}
---
MkPair True False

// Basic types and functions

type Bool { True, False }

type BoolPair { MkPair Bool Bool }

f : Int -> Int -> Int { x y -> + x y }

g : Int -> Int -> Int { x y -> - (*  x y) x }

main : BoolPair {
  // comment inside function
  MkPair True (not True)
}

not : Bool -> Bool {
  b -> match b {
    True -> False, // comment at end of line
    False -> True
  }
}

constint : Int -> Int -> Int {
  x y -> x
}

type Unit { Unit }

idunit : Unit -> Unit {
  u -> Unit
}

andpair : BoolPair -> Bool {
  p -> match p {
    MkPair a b -> and a b
  }
}

and : Bool -> Bool -> Bool {
  a b -> match a {
    True -> match b {
      True -> True,
      False -> False
    },
    False -> False
  }
}

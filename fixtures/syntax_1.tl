// Basic types and functions

type Bool { True, False }

f : Int -> Int -> Int { x y -> + x y }

g : Int -> Int -> Int { x y -> - (*  x y) x }

main : Int {
  // comment inside function
  g 4 53434
}

not : Bool -> Bool {
  b -> match b {
    True -> False, // comment at end of line
    False -> True
  }
}

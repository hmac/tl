type Bool { True, False }

type Dir { Left, Right }

foo : Bool -> Bool {
  b -> match b {
    // This constructor does not have the same type as the target
    Left -> True,
    False -> False
  }
}


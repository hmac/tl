f : List Int -> Int {
  x -> case x {
    [1, ..[2]] -> 0,
  }
}

test f { == 0 (f [1, 2]) }

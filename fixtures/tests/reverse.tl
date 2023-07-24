reverse : List a -> List a {
  l -> reverse_ l []
}

reverse_ : List a -> List a -> List a {
  l acc -> case l {
    [] -> acc,
    [x, ..xs] -> reverse_ xs [x, ..acc]
  }
}

main : List Int { reverse [3, 2, 1] }

test reverse {
  == (reverse [3, 2, 1]) [1, 2, 3]
}

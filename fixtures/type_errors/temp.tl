type List2 a { Nil2, Cons2 a (List2 a) }

convert : List a -> List2 a {
  l -> case l {
    [] -> Nil2,
    [x, ..xs] -> Cons2 x (convert xs)
  }
}

length : List a -> Int {
  l -> case l {
    [] -> 0,
    [_, ..xs] -> + 1 (length xs)
  }
}

main : Int {
  length (convert (Cons2 1 Nil2))
}
---
Error:

fixtures/type_errors/temp.tl:
  17: main : Int {
  18:   length (convert (Cons2 1 Nil2))
                         ^^^^^
                          expected this to have the type List but it actually has the type List2

type List a { Nil, Cons a (List a) }

type List2 a { Nil2, Cons2 a (List2 a) }

convert : List a -> List2 a {
  l -> case l {
    Nil -> Nil2,
    Cons x xs -> Cons2 x (convert xs)
  }
}

length : List a -> Int {
  l -> case l {
    Nil -> 0,
    Cons _ xs -> + 1 (length xs)
  }
}

main : Int {
  length (convert (Cons2 1 Nil2))
}
---
Error:

  19: main : Int {
  20:   length (convert (Cons2 1 Nil2))
                         ^^^^^
                          expected this to have the type List, but it actually has the type List2

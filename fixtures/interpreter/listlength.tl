type List { Nil, Cons Int List }

length : List -> Int {
  l -> case l {
    Nil -> 0,
    Cons _ rest -> + (length rest) 1,
  }
}

main : Int { length (Cons 1 (Cons 2 Nil)) }
---
2

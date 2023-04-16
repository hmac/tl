id : a -> a {
  x -> x
}

const : a -> b -> a {
  x y -> x
}

main : Int {
  id (id (id (const 1 2)))
}
---
1

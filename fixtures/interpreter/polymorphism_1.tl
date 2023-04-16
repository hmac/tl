apply : (a -> b) -> a -> b {
  f x -> f x
}

main : Int {
  apply (x -> + x 1) 1
}
---
2

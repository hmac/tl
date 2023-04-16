apply : (a -> b) -> a -> b {
  f x -> f x
}

applytwice : (a -> a) -> a -> a {
  f x -> f (f x)
}

main : Int {
  applytwice (x -> + x 1) 1
}
---
3

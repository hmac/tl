main : Int { id f 1 2 }

id : a -> a { f -> f }

f : Int -> (Int -> Int) { x y -> y }
---
2

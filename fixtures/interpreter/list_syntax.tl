l1 : List Int {
  let x = 4 {
    [1, 2, 3, x]
  }
}

l2 : List (List Int) {
  let x = [1, 2, 3] {
    [x, x, x]
  }
}

l3 : List Int {
  [
   1
   ,
   2,
   3,
   4,
  ]
}

main : List (List Int) { l2 }
---
[[1, 2, 3], [1, 2, 3], [1, 2, 3]]

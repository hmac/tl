main : List Int {
  let x = [2] {
    [1, ..x]
  }
}
---
[1, 2]

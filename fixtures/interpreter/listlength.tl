type IntList { IntNil, IntCons Int IntList }

length : IntList -> Int {
  l -> case l {
    IntNil -> 0,
    IntCons _ rest -> + (length rest) 1,
  }
}

main : Int { length (IntCons 1 (IntCons 2 IntNil)) }
---
2

// a regression test for a bug
// if the branches of a case bind different numbers of variables
// and we reach a join point after the case (e.g. in case-in-let)
// then our local variable number gets mixed up.

// We generate this code:
// test_f:
//   6   0: push_int 1
//   6   1: ctor "Some" 1
//   6   2: case [(Some y, 1), (None, 4)]
//   6   3: push_int 1
//   6   4: ctor "Some" 1
//   6   5: jmp 3
//   6   6: push_ctor None
//   6   7: jmp 1
//   6   8: push_int 2
//   6   9: ctor "Some" 1
//   6  10: push_var 0
//   6  11: eq
//   6  12: ret
//   6  13: ret

// The problem, I think, is that when we exit the case expression we have a different number of locals
// left on the stack depending on which branch we took.
// We need to clear these variables in order to have a consistent stack after leaving the case,
// since we don't know which branch is taken at runtime and the next instructions have to deal with either outcome.

type Option a {
  Some a,
  None
}

test f {
  let x = case Some 1 {
    Some y -> Some 2,
    None -> None
  } {
    == x (Some 2)
  }
}

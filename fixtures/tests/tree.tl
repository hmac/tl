type BinaryTree a {
  Leaf,
  Branch (BinaryTree a) a (BinaryTree a)
}

make_tree : BinaryTree a {
  Leaf
}

contains : (a -> a -> Ordering) -> a -> BinaryTree a -> Bool {
  cmp y t -> case t {
    Leaf -> False,
    Branch left x right -> case cmp y x {
      Lt -> contains cmp y left,
      Gt -> contains cmp y right,
      Eq -> True,
    }
  }
}

insert : (a -> a -> Ordering) -> a -> BinaryTree a -> BinaryTree a {
  cmp x t -> case t {
    Leaf -> Branch Leaf x Leaf,
    Branch l y r -> case cmp x y {
      Lt -> Branch (insert cmp x l) y r,
      Eq -> Branch l y r, // if element is already in the tree, don't duplicate it
      Gt -> Branch l y (insert cmp x r),
    }
  }
}

remove : (a -> a -> Ordering) -> a -> BinaryTree a -> BinaryTree a {
  cmp x t -> case t {
    Leaf -> Leaf,
    Branch l y r -> case cmp x y {
      Lt -> Branch (remove cmp x l) y r,
      Gt -> Branch l y (remove cmp x r),
      Eq ->
        // Need to merge the left and right subtrees
        // If both are leaves, just return a Leaf,
        // If one is Leaf, return the other one
        // Otherwise pick (arbitrarily) the left one to be the new root.
        case l {
          Leaf -> r,
          Branch ll lx lr -> case r {
            Leaf -> l,
            _ -> Branch ll lx (merge cmp lr r)
          }
        }
    }
  }
}

merge : (a -> a -> Ordering) -> BinaryTree a -> BinaryTree a -> BinaryTree a {
  cmp l r -> 
    case l {
      Leaf -> r,
      Branch ll lx lr -> 
        case r {
          Leaf -> l,
          Branch rl rx rr ->
            case cmp lx rx {
              Eq -> Branch (merge cmp ll rl) lx (merge cmp lr rr),
              Lt -> Branch (merge cmp l rl) rx rr,
              Gt -> Branch rl rx (merge cmp l rr),
            }
        }
    }
}

insert_last_unchecked : a -> BinaryTree a -> BinaryTree a {
  x t -> case t {
    Leaf -> Branch Leaf x Leaf,
    Branch l y r -> Branch l y (insert_last_unchecked x r)
  }
}

to_list : BinaryTree a -> List a {
  t -> case t {
    Leaf -> [],
    Branch l x r -> append (to_list l) [x, ..to_list r]
  }
}

from_list : (a -> a -> Ordering) -> List a -> BinaryTree a {
  cmp l -> case l {
    [] -> make_tree,
    [x, ..xs] -> insert cmp x (from_list cmp xs)
  }
}

from_ordered_list : List a -> BinaryTree a {
  l -> case l {
    [] -> make_tree,
    [x, ..xs] -> insert_last_unchecked x (from_ordered_list xs)
  }
}

append : List a -> List a -> List a {
  l1 l2 -> case l1 {
    [] -> l2,
    [x, ..xs] -> [x, ..append xs l2]
  }
}

type Ordering {
  Lt,
  Gt,
  Eq
}

or : Bool -> Bool -> Bool {
  a b -> case a {
    True -> True,
    False -> b
  }
}

cmp_int : Int -> Int -> Ordering {
  x y -> case == x y {
    True -> Eq,
    False -> case < x y {
      True -> Lt,
      False -> Gt,
    }
  }
}

test contains_1 {
  let t1 = insert cmp_int 1 make_tree {
    let t2 = insert cmp_int 2 t1 {
      let t3 = insert cmp_int 3 t2 {
        contains cmp_int 3 t3
      }
    }
  }
}

test contains_2 {
  let t = insert cmp_int 1
    (insert cmp_int 2
      (insert cmp_int 3
        (insert cmp_int 4 make_tree)
      )
    ) {
    contains cmp_int 2 t
  }
}

test to_list_1 {
  let t = insert cmp_int 1 (insert cmp_int 3 (insert cmp_int 2 make_tree)) {
    == (to_list t) [1, 2, 3]
  }
}

test from_list_to_list_roundtrip {
  == [1, 2, 3] (to_list (from_list cmp_int [1, 2, 3]))
}

size : BinaryTree a -> Int {
  t -> case t {
    Leaf -> 0,
    Branch l x r -> + (+ (size l) (size r)) 1
  }
}

test size_1 { == 6 (size (from_ordered_list [1,2,3,4,5,6])) }
test size_2 { == 0 (size make_tree)  }
test size_3 { == 3 (size (from_list cmp_int [1,2,2,2,2,6])) }

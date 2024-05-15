use ./list.tl as list

type Ordering {
  Lt,
  Gt,
  Eq
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

type Colour { Red, Black }

type Tree k v {
  Leaf,
  Node Colour (Tree k v) k v (Tree k v)
}

make_tree : Tree k v { Leaf }

is_red : Tree k v -> Bool {
  t -> case t { Node Red _ _ _ _ -> True, _ -> False }
}

bal_left : Tree k v -> k -> v -> Tree k v -> Tree k v {
  l k v r -> case l {
    Leaf -> Leaf,
    Node _ (Node Red lx kx vx rx) ky vy ry ->
      Node Red (Node Black lx kx vx rx) ky vy (Node Black ry k v r),
    Node _ ly ky vy (Node Red lx kx vx rx) ->
      Node Red (Node Black ly ky vy lx) kx vx (Node Black rx k v r),
    Node _ lx kx vx rx -> Node Black (Node Red lx kx vx rx) k v r
  }
}

bal_right : Tree k v -> k -> v -> Tree k v -> Tree k v {
  l k v r -> case r {
    Leaf -> Leaf,
    Node _ (Node Red lx kx vx rx) ky vy ry ->
      Node Red (Node Black l k v lx) kx vx (Node Black rx ky vy ry),
    Node _ lx kx vx (Node Red ly ky vy ry) ->
      Node Red (Node Black l k v lx) kx vx (Node Black ly ky vy ry),
    Node _ lx kx vx rx ->
      Node Black l k v (Node Red lx kx vx rx)
  }
}

insert_ : (k -> k -> Ordering) -> Tree k v -> k -> v -> Tree k v {
  cmp t k v -> case t {
    Leaf -> Node Red Leaf k v Leaf,
    Node Red l kx vx r -> case cmp k kx {
      Lt -> Node Red (insert_ cmp l k v) kx vx r,
      Eq -> Node Red l k v r,
      Gt -> Node Red l kx vx (insert_ cmp r k v),
    },
    Node Black l kx vx r -> case cmp k kx {
      Lt -> case is_red l {
        True -> bal_left (insert_ cmp l k v) kx vx r,
        False -> Node Black (insert_ cmp l k v) kx vx r,
      },
      Eq -> Node Black l k v r,
      Gt -> Node Black l kx vx (insert_ cmp r k v),
    }
  }
}

set_black : Tree k v -> Tree k v {
  t -> case t {
    Node _ l k v r -> Node Black l k v r,
    _ -> t
  }
}

insert : (k -> k -> Ordering) -> k -> v -> Tree k v -> Tree k v {
  cmp k v t -> case is_red t {
    True -> set_black (insert_ cmp t k v),
    False -> insert_ cmp t k v
  }
}

type Option a { None, Some a }

lookup : (k -> k -> Ordering) -> k -> Tree k v -> Option v {
  cmp k t -> case t {
    Leaf -> None,
    Node _ l kx vx r -> case cmp k kx {
      Lt -> lookup cmp k l,
      Eq -> Some vx,
      Gt -> lookup cmp k r,
    }
  }
}

test lookup_1 {
  let t = insert cmp_int 1 True
    (insert cmp_int 2 False
    (insert cmp_int 3 True make_tree)) {
    == (lookup cmp_int 3 t) (Some True)
  }
}

test lookup_2 {
  let t = insert cmp_int 1 True
    (insert cmp_int 2 False
    (insert cmp_int 3 True make_tree)) {
    == (lookup cmp_int 4 t) None
  }
}

size : Tree k v -> Int {
  t -> case t {
    Leaf -> 0,
    Node _ l _ _ r -> + (+ (size l) (size r)) 1
  }
}

to_list : Tree k v -> List (k, v,) {
  t -> case t {
    Leaf -> [],
    Node _ l k v r ->
      let list_l = to_list l,
          list_r = to_list r {
      list.append (to_list l) [(k, v,), ..to_list r]
    }
  }
}

from_list : (k -> k -> Ordering) -> List (k, v,) -> Tree k v {
  ord l -> list.foldl (t kv -> case kv { (k, v,) -> insert ord k v t }) make_tree l
}

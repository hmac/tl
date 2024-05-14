use ./red_black_tree.tl as tree

type Map k v {
  Map (k -> k -> tree.Ordering) (tree.Tree k v)
}

new : (k -> k -> tree.Ordering) -> Map k v {
  ord -> Map ord tree.make_tree
}

insert : k -> v -> Map k v -> Map k v {
  k v m -> case m {
    Map ord t -> Map ord (tree.insert ord k v t)
  }
}

lookup : k -> Map k v -> tree.Option v {
  k m -> case m {
    Map ord t -> tree.lookup ord k t
  }
}

size : Map k v -> Int {
  m -> case m {
    Map _ t -> tree.size t
  }
}

to_list : Map k v -> List (k, v,) {
  m -> case m {
    Map _ t -> tree.to_list t
  }
}

from_list : (k -> k -> tree.Ordering) -> List (k, v,) -> Map k v {
  ord l -> Map ord (tree.from_list ord l)
}

test to_list_empty {
  == (to_list (new tree.cmp_int)) []
}

test from_list_to_list {
  let unsorted = [(1, "a"), (9, "b"), (2, "c"), (8, "d"), (3, "e"), (7, "f"), (4, "g"), (6, "h"), (5, "i")],
      sorted = [(1, "a"), (2, "c"), (3, "e"), (4, "g"), (5, "i"), (6, "h"), (7, "f"), (8, "d"), (9, "b")] {
    == (to_list (from_list tree.cmp_int unsorted)) sorted
  }
}

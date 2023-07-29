map : (a -> b) -> List a -> List b {
  f l -> case l {
    [] -> [],
    [x, ..xs] -> [f x, ..map f xs],
  }
}

test map {
  == (map (x -> + x 1) [1, 2, 3])
    [2, 3, 4]
}

foldl : (b -> a -> b) -> b -> List a -> b {
  f z l -> case l {
    [] -> z,
    [x, ..xs] -> f (foldl f z xs) x
  }
}

test foldl {
  == (foldl (x y -> * x y) 1 [1, 2, 3, 4]) 24
}

test foldl_empty { == (foldl (a x -> + a x) 0 []) 0 }

test foldl_list { == (foldl (a x -> [x, ..a]) [] [1, 2, 3]) [1, 2, 3] }

filter : (a -> Bool) -> List a -> List a {
  p l -> foldl (acc x -> case p x { True -> [x, ..acc], False -> acc }) [] l
}

test filter {
  == (filter (x -> == x 3) [1, 2, 3, 4]) [3]
}

zip_with : (a -> b -> c) -> List a -> List b -> List c {
  f ls rs -> case ls {
    [] -> [],
    [x, ..xs] -> case rs {
      [] -> [],
      [y, ..ys] -> [f x y, ..zip_with f xs ys]
    }
  }
}

test zip_with {
  == (zip_with (x y -> + x y) [1, 2, 3] [4, 5, 6]) [5, 7, 9]
}

type Pair a b { Pair a b }

zip : List a -> List b -> List (Pair a b) {
  ls rs -> zip_with (x y -> Pair x y) ls rs
}

test zip {
  == (zip [1, 2, 3] [4, 5, 6]) [Pair 1 4, Pair 2 5, Pair 3 6]
}

len : List a -> Int { len_helper 0 }

len_helper : Int -> List a -> Int {
  acc l -> case l {
    [] -> acc,
    [_, ..rest] -> len_helper (+ acc 1) rest
  }
}

test len {
  == (len [1, 2, 3]) 3
}

append : List a -> List a -> List a {
  ls rs -> case ls {
    [] -> rs,
    [x, ..xs] -> [x, ..append xs rs]
  }
}

test append {
  == (append [1, 2, 3] [4, 5, 6]) [1, 2, 3, 4, 5, 6]
}

type Option a { None, Some a }

first : List a -> Option a {
  l -> case l {
    [] -> None,
    [x, .._] -> Some x,
  }
}

test first { == (first [1, 2]) (Some 1) }
test first_empty { == (first []) None }

last : List a -> Option a {
  l -> case l {
    [] -> None,
    [x] -> Some x,
    [_, ..r] -> last r,
  }
}

test last { == (last [1, 2]) (Some 2) }
test last_one { == (last [1]) (Some 1) }
test last_empty { == (last []) None }

tail : List a -> Option (List a) {
  l -> case l {
    [] -> None,
    [x, ..rest] -> Some rest,
  }
}

test tail { == (tail [1, 2, 3]) (Some [2, 3]) }
test tail_empty { == (tail []) None }

init : List a -> Option (List a) {
  l -> case l {
    [] -> None,
    [x, ..xs] -> Some (init_helper x xs)
  }
}

init_helper : a -> List a -> List a {
  x l -> case l {
    [] -> [],
    [y, ..ys] -> [x, ..init_helper y ys]
  }
}

test init { == (init [1, 2, 3]) (Some [1, 2]) }
test init_empty { == (init []) None }
test init_single { == (init [1]) (Some []) }

single : a -> List a {
  x -> [x]
}

test single { == (single 1) [1] }

empty : List a -> Bool {
  l -> case l { [] -> True, _ -> False }
}

test empty_empty { == (empty []) True }
test empty_nonempty { == (empty [1]) False }

reverse : List a -> List a {
  l -> reverse_helper l []
}

reverse_helper : List a -> List a -> List a {
  l r -> case l {
    [] -> r,
    [x, ..xs] -> reverse_helper xs ([x, ..r])
  }
}

test reverse { == (reverse [1, 2, 3]) [3, 2, 1] }
test reverse_empty { == (reverse []) [] }

intersperse : a -> List a -> List a {
  sep l -> case l {
    [] -> [],
    [x] -> [x],
    [x, ..xs] -> [x, sep, ..intersperse sep xs]
  }
}

test intersperse {
  == (intersperse 9 [1, 2, 3]) [1, 9, 2, 9, 3]
}

unzip : List (Pair a b) -> Pair (List a) (List b) {
  let f : Pair a b -> Pair (List a) (List b) -> Pair (List a) (List b) =
    ab asbs -> case ab {
      Pair a b -> case asbs {
        Pair as bs -> Pair [a, ..as] [b, ..bs]
      }
    }
  { foldr f (Pair [] []) }
}


test_unzip_single { == (unzip [Pair 1 2]) (Pair [1] [2]) }
test_unzip { == (unzip [Pair 1 2, Pair 3 4]) (Pair [1, 3] [2, 4]) }

foldr : (a -> b -> b) -> b -> List a -> b {
  f z l -> case l {
    [] -> z,
    [x, ..xs] -> f x (foldr f z xs)
  }
}

test foldr_list { == (foldr (x a -> [x, ..a]) [] [1, 2, 3]) [1, 2, 3] }
test foldr_list_empty { == (foldr (x a -> [x, ..a]) [] []) [] }

subsequences : List a -> List (List a) {
  l -> case l {
    [] -> [],
    [x, ..xs] -> [[x], ..foldr (ys r -> [ys, [x, ..ys], ..r]) [] (subsequences xs)]
  }
}

test_subsequences {
  == (subsequences [1, 2, 3])
    [[1], [2], [1, 2], [3], [1, 3], [2, 3], [1, 2, 3]]
}


// Taken from the Haskell implementation.
// Don't fully understand how this works.
permutations : List a -> List (List a) {
  xs0 -> [xs0, ..perms xs0 []]
}

// The next three functions are helpers for permutations.
// interleave_ and perms are recursive, so can't be let-bound (yet).
id : a -> a { x -> x }

interleave_ : a -> List a -> (List a -> b) -> List a -> List b -> Pair (List a) (List b) {
  t ts f l r -> case l {
    [] -> Pair ts r,
    [y, ..ys] -> case interleave_ t ts (x -> f [y, ..x]) ys r {
      Pair us zs -> Pair [y, ..us] [f [t, y, ..us], ..zs]
    }
  }
}

perms : List a -> List a -> List (List a) {
  l is -> case l {
    [] -> [],
    [t, ..ts] ->
      let
        interleave : List a -> List (List a) -> List (List a)
          = xs r -> case interleave_ t ts id xs r { Pair _ zs -> zs },
      { foldr interleave (perms ts [t, ..is]) (permutations is) }
  }
}

test permutations {
  == (permutations [1, 2, 3])
    [[1, 2, 3], [2, 1, 3], [3, 2, 1], [2, 3, 1], [3, 1, 2], [1, 3, 2]]
}

test permutations_empty {
  == (permutations []) [[]]
}

// Disabled because it takes a few seconds to run.
// test permutations_large {
//   == (len (permutations [1, 2, 3, 4, 5, 6])) 720
// }

concat : List (List a) -> List a {
  foldr (x y -> foldr (a xs -> [a, ..xs]) y x) []
}

test concat { == (concat [[1, 2, 3], [4, 5], [6], []]) [1, 2, 3, 4, 5, 6] }
test concat_empty { == (concat []) []}

concat_map : (a -> List b) -> List a -> List b {
  f l -> concat (map f l)
}

test concat_map {
  == (concat_map (x -> [x, + x 1]) [1, 2, 3]) [1, 2, 2, 3, 3, 4]
}
test concat_map_empty {
  == (concat_map (x -> []) []) []
}

and : Bool -> Bool -> Bool {
  x y -> case x {
    False -> False,
    True -> y
  }
}

all_true : List Bool -> Bool { foldl and True }

test all_true_false { == (all_true [True, True, False, True]) False }
test all_true_true { == (all_true [True, True, True, True]) True }

sum : List Int -> Int {
  foldl (+) 0
}

all : (a -> Bool) -> List a -> Bool {
  p -> foldr (b acc -> and (p b) acc) True
}

test all {
  == (all (xs -> == (sum xs) 4) [[1, 3], [2, 2], [0, 4]]) True
}

map_accum_l : (s -> a -> Pair s b) -> s -> List a -> Pair s (List b) {
  f z l -> foldl (acc x -> case acc {
    Pair r l2 ->
      let y = f r x {
        case y {
          Pair r2 y2 -> Pair r2 [y2, ..l2]
        }
      }
    }
  ) (Pair z []) l
}

// test map_accum_l { == (Pair 10 [0, 1, 3, 6]) (map_accum_l (a b -> Pair (+ a b) a) 0 [1, 2, 3, 4]) }

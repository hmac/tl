use ./option.tl as opt

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

zip : List a -> List b -> List (a, b) {
  ls rs -> zip_with (x y -> (x, y)) ls rs
}

test zip {
  == (zip [1, 2, 3] [4, 5, 6]) [(1, 4), (2, 5), (3, 6)]
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

first : List a -> opt.Option a {
  l -> case l {
    [] -> opt.None,
    [x, .._] -> opt.Some x,
  }
}

test first { == (first [1, 2]) (opt.Some 1) }
test first_empty { == (first []) opt.None }

last : List a -> opt.Option a {
  l -> case l {
    [] -> opt.None,
    [x] -> opt.Some x,
    [_, ..r] -> last r,
  }
}

test last { == (last [1, 2]) (opt.Some 2) }
test last_one { == (last [1]) (opt.Some 1) }
test last_empty { == (last []) opt.None }

tail : List a -> opt.Option (List a) {
  l -> case l {
    [] -> opt.None,
    [x, ..rest] -> opt.Some rest,
  }
}

test tail { == (tail [1, 2, 3]) (opt.Some [2, 3]) }
test tail_empty { == (tail []) opt.None }

init : List a -> opt.Option (List a) {
  l -> case l {
    [] -> opt.None,
    [x, ..xs] -> opt.Some (init_helper x xs)
  }
}

init_helper : a -> List a -> List a {
  x l -> case l {
    [] -> [],
    [y, ..ys] -> [x, ..init_helper y ys]
  }
}

test init { == (init [1, 2, 3]) (opt.Some [1, 2]) }
test init_empty { == (init []) opt.None }
test init_single { == (init [1]) (opt.Some []) }

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

unzip : List (a, b) -> (List a, List b) {
  let f : (a, b) -> (List a, List b) -> (List a, List b) =
    ab asbs -> case ab {
      (a, b) -> case asbs {
        (as, bs) -> ([a, ..as], [b, ..bs])
      }
    }
  { foldr f ([], []) }
}


test_unzip_single { == (unzip [(1, 2)]) ([1], [2]) }
test_unzip { == (unzip [(1, 2), (3, 4)]) ([1, 3], [2, 4]) }

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

interleave_ : a -> List a -> (List a -> b) -> List a -> List b -> (List a, List b) {
  t ts f l r -> case l {
    [] -> (ts, r),
    [y, ..ys] -> case interleave_ t ts (x -> f [y, ..x]) ys r {
      (us, zs) -> ([y, ..us], [f [t, y, ..us], ..zs])
    }
  }
}

perms : List a -> List a -> List (List a) {
  l is -> case l {
    [] -> [],
    [t, ..ts] ->
      let
        interleave : List a -> List (List a) -> List (List a)
          = xs r -> case interleave_ t ts id xs r { (_, zs) -> zs },
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

map_accum_l : (s -> a -> (s, b)) -> s -> List a -> (s, List b) {
  f z l -> foldl (acc x -> case acc {
    (r, l2) ->
      let y = f r x {
        case y {
          (r2, y2) -> (r2, [y2, ..l2])
        }
      }
    }
  ) (z, []) l
}

// Possibly this shouldn't be backwards
test map_accum_l {
  == (10, [9, 7, 4, 0])
  (map_accum_l (a b -> (+ a b, a)) 0 [1, 2, 3, 4])
}

seq_opt : List (opt.Option a) -> opt.Option (List a) {
  xs -> case xs {
    [] -> opt.Some [],
    [x, ..r] -> case x {
      opt.Some y -> case seq_opt r {
        opt.None -> opt.None,
        opt.Some zs -> opt.Some [y, ..zs]
      }
      // note: if this branch is missing, the compiler doesn't notice
      opt.None -> opt.None,
    }
  }
}

test seq_opt {
  == [opt.Some [1,2,3], opt.None] (map seq_opt [
    [opt.Some 1, opt.Some 2, opt.Some 3],
    [opt.Some 1, opt.None, opt.Some 3],
  ])
}

any : (a -> Bool) -> List a -> Bool {
  f xs -> case xs {
    [] -> False,
    [x, ..r] -> case f x {
      True -> True,
      False -> any f r
    }
  }
}



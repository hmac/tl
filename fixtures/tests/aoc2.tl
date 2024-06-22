use ./option.tl as opt
use ./list.tl as list
use ./aoc2_input.tl as aoc2_input

test char_at_0 {
  == 'a' (char_at 0 "abc")
}

test char_at_1 {
  == 'b' (char_at 1 "abc")
}

test char_at_2 {
  == 'c' (char_at 2 "abc")
}

test char_at_3 {
  == 'a' (char_at 3 "abc")
}

input_small : List String {
  [
    "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green",
    "Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue",
    "Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red",
    "Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red",
    "Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green"
  ]
}

parse_digits : Int -> String -> (List Int, Int) {
  parse_digits_ []
}

parse_digits_ : List Int -> Int -> String -> (List Int, Int) {
  acc n s -> case to_digit (char_at n s) {
    opt.None -> (acc, n),
    opt.Some i -> parse_digits_ [i, ..acc] (+ n 1) s
  }
}

// Returns (parsed integer, index of char after last digit)
parse_int : Int -> String -> (Int, Int) {
  n s -> case parse_digits n s {
    (digits, n2) -> (digits_to_int digits, n2)
  }
}

test parse_int {
  == (1, 6) (parse_int 5 "Game 1:")
}

test parse_game_id {
  let x = case list.first input_small {
    opt.Some i -> opt.Some (parse_int 5 i),
    opt.None -> opt.None
  } {
    == (opt.Some (1, 6)) x
  }
}

digits_to_int : List Int -> Int {
  list.foldl (acc n -> + n (* acc 10)) 0
}

to_digit : Char -> opt.Option Int {
 c -> first_true c [('0', 0), ('1', 1), ('2', 2), ('3', 3), ('4', 4), ('5', 5), ('6', 6), ('7', 7), ('8', 8), ('9', 9)]
}

first_true : Char -> List (Char, Int) -> opt.Option Int {
 c1 l -> case l {
  [] -> opt.None,
  [(c2, n), ..r] -> case == c1 c2 {
   True -> opt.Some n,
   False -> first_true c1 r
  }
 }
}

type Colour { Red, Blue, Green }

parse_game_from_index_ : Int -> String -> List (Colour, Int) -> opt.Option (Int, List (Colour, Int)) {
  n s acc -> case parse_int n s {
    // skip the single space char
    (num, n2) -> case parse_colour (+ n2 1) s {
      opt.None -> opt.None,
      opt.Some j -> case j {
        (colour, n3) -> let end = char_at n3 s {
          case == end ',' {
            True -> parse_game_from_index_ (+ n3 2) s [(colour, num), ..acc],
            False -> case == end ';' {
              True -> opt.Some (+ n3 1, [(colour, num), ..acc]),
              False -> opt.Some (n3, [(colour, num), ..acc])
            }
          }
        }
      }
    }
  }
}

parse_game_from_index : Int -> String -> opt.Option (Int, List (Colour, Int)) {
  n s -> parse_game_from_index_ n s []
}

test parse_game_from_index {
  == (opt.Some (14, [(Blue, 4), (Red, 3)])) (parse_game_from_index 0 "3 red, 4 blue;")
}

test parse_game_from_index_2 {
  == (opt.Some (13, [(Blue, 4), (Red, 3)])) (parse_game_from_index 0 "3 red, 4 blue")
}

parse_games : String -> opt.Option (Int, List (List (Colour, Int))) {
  s -> case parse_int 5 s {
    (game_id, n) -> case parse_games_ (+ n 2) s {
      opt.Some games -> opt.Some (game_id, games),
      opt.None -> opt.None
    }
  }
}

parse_games_ : Int -> String -> opt.Option (List (List (Colour, Int))) {
  parse_games__ []
}

parse_games__ : List (List (Colour, Int)) -> Int -> String -> opt.Option (List (List (Colour, Int))) {
  acc n s -> case parse_game_from_index n s {
    opt.Some t -> case t {
      (n2, game) -> parse_games__ [game, ..acc] (+ n2 1) s
    },
    opt.None -> opt.Some acc
  }
}

test parse_games {
  == (parse_games "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green") (opt.Some (1, [[(Green, 2)], [(Blue, 6), (Green, 2), (Red, 1)], [(Red, 4), (Blue, 3)]]))
}

// (red, green, blue)
games_breach_cube_limit : (Int, Int, Int) -> List (List (Colour, Int)) -> Bool {
  lim games -> any (game_breaches_limit lim) games
}

game_breaches_limit : (Int, Int, Int) -> List (Colour, Int) -> Bool {
  lim game -> case lim {
    (r_lim, g_lim, b_lim) -> case game {
      [] -> False,
      [t, ..r] -> case t {
        (c, n) -> case c {
          Red -> case < r_lim n {
            True -> True,
            False -> game_breaches_limit lim r,
          },
          Green -> case < g_lim n {
            True -> True,
            False -> game_breaches_limit lim r,
          },
          Blue -> case < b_lim n {
            True -> True,
            False -> game_breaches_limit lim r,
          }
        }
      }
    }
  }
}

test game_breaches_limit {
  == [True, False] (list.map (game_breaches_limit (2, 3, 4)) [
    [(Red, 2), (Green, 4), (Blue, 4)],
    [(Red, 2), (Green, 2), (Blue, 1)]
  ])
}

test games_breach_cube_limit {
  == True (games_breach_cube_limit (2, 3, 4) [
    [(Red, 2), (Green, 2), (Blue, 1)],
    [(Red, 2), (Green, 4), (Blue, 4)],
  ])
}

filter : (a -> Bool) -> List a -> List a {
  p xs -> case xs {
    [] -> [],
    [x, ..r] -> case p x {
      True -> [x, ..filter p r],
      False -> filter p r
    }
  }
}

sequenceOpt : List (opt.Option a) -> opt.Option (List a) {
  xs -> case xs {
    [] -> opt.Some [],
    [x, ..r] -> case x {
      opt.Some y -> case sequenceOpt r {
        opt.None -> opt.None,
        opt.Some zs -> opt.Some [y, ..zs]
      }
    }
  }
}

uncurry: (a -> b -> c) -> (a, b) -> c {
  f t -> case t {
    (x, y) -> f x y
  }
}

not : Bool -> Bool { b -> case b { True -> False, False -> True } }

possible_games : List String -> opt.Option (List Int) {
  let possible : Int -> List (List (Colour, Int)) -> Bool
               = id games -> not (games_breach_cube_limit (12, 13, 14) games) {
    game_strings -> let parsed = sequenceOpt (list.map parse_games game_strings),
                        filterAndGetId : List (Int, List (List (Colour, Int))) -> List Int = games -> list.map fst (filter (uncurry possible) games) {
                      opt.map filterAndGetId parsed
                    }
  }
}

sum : List Int -> Int {
  list.foldl (x y -> + x y) 0
}

answer_small : opt.Option Int {
  opt.map sum (possible_games input_small)
}

answer_big : opt.Option Int {
  opt.map sum (possible_games aoc2_input.aoc2_input)
}

test answer_small {
  == answer_small (opt.Some 8)
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


first : (a -> opt.Option b) -> List a -> opt.Option (a, b) {
  f xs -> case xs {
    [] -> opt.None,
    [x, ..z] -> case f x {
      opt.Some r -> opt.Some (x, r),
      opt.None -> first f z
    }
  }
}

snd : (a, b) -> b {
  t -> case t { (x, y) -> y }
}

fst : (a, b) -> a {
  t -> case t { (x, y) -> x }
}

mapFst : (a -> b) -> (a, c) -> (b, c) {
  f t -> case t { (x, y) -> (f x, y) }
}

parse_colour : Int -> String -> opt.Option (Colour, Int) {
  n s -> opt.map (mapFst snd) (first (t -> parse_word n s (fst t)) [("red", Red), ("green", Green), ("blue", Blue)])
}

test parse_colour {
  == (opt.Some (Green, 7)) (parse_colour 2 "a green frog")
}

parse_word : Int -> String -> String -> opt.Option Int {
  n s word -> parse_word_ 0 (list.len (chars word)) word n s
}

// note: does not check if we have reached the end of the string
parse_word_ : Int -> Int -> String -> Int -> String -> opt.Option Int {
  word_n word_len word str_n str -> case == word_n word_len {
    // we have parsed the whole word
    True -> opt.Some str_n,
    False -> case (== (char_at str_n str) (char_at word_n word)) {
      True -> parse_word_ (+ word_n 1) word_len word (+ str_n 1) str,
      False -> opt.None
    }
  }
}

type Option a { Some a, None }

// no-target case as a function body
unwrap_or : Int -> Option Int -> Int {
  default -> case {
    Some n -> n,
    None -> default
  }
}

test unwrap_some { == 5 (unwrap_or 0 (Some 5)) }
test unwrap_none { == 0 (unwrap_or 0 None) }

// no-target case with tuple patterns
fst : (a, b) -> a { case { (x, _) -> x } }
snd : (a, b) -> b { case { (_, y) -> y } }

test fst { == 1 (fst (1, 2)) }
test snd { == 2 (snd (1, 2)) }

// no-target case with list patterns
is_empty : List a -> Bool {
  case {
    [] -> True,
    _ -> False
  }
}

test is_empty_nil { is_empty [] }
test is_empty_cons { == False (is_empty [1]) }

// no-target case with nested patterns
head : List a -> Option a {
  case {
    [] -> None,
    [x, .._] -> Some x
  }
}

test head_empty { == None (head []) }
test head_nonempty { == (Some 1) (head [1, 2, 3]) }

// no-target case with wildcard
always_zero : Option Int -> Int { case { _ -> 0 } }

test always_zero { == 0 (always_zero (Some 5)) }

// no-target case passed as an argument
map_option : (a -> b) -> Option a -> Option b {
  f opt -> case opt {
    Some x -> Some (f x),
    None -> None
  }
}

add1 : Int -> Int { x -> + x 1 }

test map_option_some { == (Some 6) (map_option add1 (Some 5)) }

// no-target case with closures (capturing a free variable)
contains : Int -> List Int -> Bool {
  needle -> case {
    [] -> False,
    [x, ..xs] -> case (== x needle) {
      True -> True,
      False -> contains needle xs
    }
  }
}

test contains_found { contains 2 [1, 2, 3] }
test contains_missing { == False (contains 4 [1, 2, 3]) }

// lambda-case passed directly as an argument to a higher-order function
map : (a -> b) -> List a -> List b {
  f l -> case l {
    [] -> [],
    [x, ..xs] -> [f x, ..map f xs]
  }
}

test map_lambda_case {
  == [2, 3, 4] (map (case { x -> + x 1 }) [1, 2, 3])
}

test map_option_lambda_case {
  == (Some 6) (map_option (case { x -> + x 1 }) (Some 5))
}

// lambda-case with Bool patterns
negate : Bool -> Bool {
  case {
    True -> False,
    False -> True
  }
}

test negate_true { == False (negate True) }
test negate_false { negate False }

// lambda-case with int literal patterns
describe : Int -> Bool {
  case {
    0 -> False,
    _ -> True
  }
}

test describe_zero { == False (describe 0) }
test describe_nonzero { describe 42 }

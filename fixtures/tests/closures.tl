f : String -> String -> Bool {
  x y -> True
}

g : String -> Bool {
  f "abc"
}

test g {
  g "def"
}

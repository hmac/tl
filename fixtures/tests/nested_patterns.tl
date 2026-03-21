type Foo { Done, More Int Foo }

f : Foo -> Int {
  case {
    More x (More y Done) -> + x y,
    _ -> 0,
  }
}

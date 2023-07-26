type Foo { Done, More Int Foo }

f : Foo -> Int {
  g -> case g {
    More x (More y Done) -> + x y,
    _ -> 0,
  }
}

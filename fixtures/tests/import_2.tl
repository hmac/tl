use ./import_1.tl as imp

baz : Bool -> MyType {
  b -> case b { True -> imp.Foo, False -> imp.NoFoo }
}

test bar { == 1 (imp.bar (baz True)) }

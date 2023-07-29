use ./import_1.tl as imp

baz : Bool -> MyType {
  b -> case b { True -> Foo, False -> Foo }
}

test bar { == 1 (bar (baz True)) }

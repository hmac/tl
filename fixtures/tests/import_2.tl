use ./import_1.tl as imp

baz : Bool -> imp.MyType {
  case { True -> imp.Foo, False -> imp.NoFoo }
}

isFoo : imp.MyType -> Bool {
  case {
    imp.Foo -> True,
    _ -> False
  }
}

test bar { == 1 (imp.bar (baz True)) }

test isFoo { == True (isFoo imp.Foo) }

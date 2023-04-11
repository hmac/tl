type Bool { True, False }

f : Int -> Int -> Int { x y -> + x y }

g : Int -> Int -> Int { x y -> - (*  x y) x }

main : Int {
  g 4 53434
}

//apply : (a -> b) -> a -> b {
//  f x -> f x
//}
//
//apply2 : (a -> a) -> a -> a {
//  f x -> f (f x)
//}
//
//type List a {
//  Nil,
//  Cons a (List a)
//}
//
//empty : List a -> Bool {
//  list -> match list {
//    Nil -> True,
//    Cons x xs -> False
//  }
//}
//
//not : Bool -> Bool {
//  b -> match b {
//    True -> False,
//    False -> True
//  }
//}
//  
//not_empty : List a -> Bool {
//  list -> not (empty list)
//}

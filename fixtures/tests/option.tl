type Option a {
  None,
  Some a
}

map : (a -> b) -> Option a -> Option b {
  f o -> case o {
    Some x -> Some (f x),
    None -> None
  }
}

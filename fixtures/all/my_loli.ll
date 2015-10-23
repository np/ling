my_loli = \(S : Session)(T : Session) -> {~S,T}

test_my_loli =
  proc(c : my_loli (!Int) (!Int))
  c{i,o}
  recv i (x : Int).
  send o x

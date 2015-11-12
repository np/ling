my_loli = \(S T : Session) -> {~S,T}

test_my_loli =
 \(A : Type)->
  proc(c : my_loli (!A) (!A))
  c{i,o}
  recv i (x : A).
  send o x

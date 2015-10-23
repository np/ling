my_dual = \(S : Session)-> ~S

test_my_dual = proc(c : my_dual (!Int))
  recv c (x : Int)

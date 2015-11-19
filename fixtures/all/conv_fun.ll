conv_fun =
  \ (A A' B : Type)
    (S : Session)
    (dom : A' -> A)
    (cod : B -> < S >)
    (f   : A -> B)->
  proc(c : !A' -o S)
    c{i,o}
    recv i (p : A')
    @(cod (f (dom p)))(o)

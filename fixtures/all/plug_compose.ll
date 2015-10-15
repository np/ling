plug_compose =
  \(A : Session)
   (B : Session)
   (C : Session)
   (p : < A, B >)
   (q : < ~B, C >)->
  proc(a : A, c : C)
    new(b : B, b' : ~B)
    ( @p(a, b)
    | @q(b', c))

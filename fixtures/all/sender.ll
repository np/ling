test_sender =
  \(A : Type)
   (S : A -> Session)
   (t : A)
   (p : < S t >)->
    proc(c)
      c : !(x : A). S x <- t.
      @p(c)

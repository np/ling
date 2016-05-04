test_receiver =
  \(A : Type)
   (S : A -> Session)
   (p : (x : A)-> < S x >)->
  proc(c)
    let x : A <- c.
    @(p x)(c)

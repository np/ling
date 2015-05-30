id : (A : Type)(x : A) -> A.

idproc (c : ?Int, d : !Int) =
  recv c (y : Int)
  send d (id Int y).

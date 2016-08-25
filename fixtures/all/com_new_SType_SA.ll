com_new_SType_SA =
  proc ()
  new/fuse 1 [c : !(A : Type).!A, d : ?(A : Type).?A].
  ( c : !(A : Type).!A <- Int.
    c <- 42
  | let B : Type <- d.
    let x : B <- d)

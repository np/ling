com_new_SInt_RBool2 = proc ()
  new/fuse1 [c : !Int.?Bool, d : ?Int.!Bool].
  ( c <- 42.
    let b : Bool <- c
  | let x : Int <- d.
    d <- `true)

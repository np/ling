com_new =
 \(S : Session)
  (p : < S  >)
  (q : < ~S >)
  (ann : Allocation)->
  proc()
  new/ann [c : S, d : ~S].
  ( @p(c)
  | @q(d))

com_new_SInt =
  com_new
    (!Int)
    (proc(c' : !Int) c' <- 42)
    (proc(d : ?Int) let x : Int <- d)

com_new_SInt_alloc = com_new_SInt alloc
com_new_SInt_fuse1 = com_new_SInt fuse1

com_new_SInt_RBool =
  com_new
    (!Int.?Bool)
    (proc(c' : !Int.?Bool) c' <- 42. let b : Bool <- c')
    (proc(d : ?Int.!Bool) let x : Int <- d. d <- `true)

com_new_SInt_RBool_alloc = com_new_SInt_RBool alloc
com_new_SInt_RBool_fuse1 = com_new_SInt_RBool fuse1
com_new_SInt_RBool_fuse2 = com_new_SInt_RBool fuse2
com_new_SInt_RBool_fuse3 = com_new_SInt_RBool fuse3

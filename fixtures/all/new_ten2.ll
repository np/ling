new_ten2 =
  \(A B : Session)
   (pA  : < A >)
   (pB  : < B >)
   (pC  : < {~A,~B} >)
   (ann : Allocation)->
  proc()
    new/ann [ab : [A,B], nab : {~A,~B}].
    ( split ab as [a,b].
      ( @(pA)(a)
      | @(pB)(b))
    | @(pC)(nab))

new_ten2_Int_dbl =
  new_ten2 (!Int) (?Int) (proc(c) c <- 42) (proc(d) let b : Int <- d)
           (proc(nab)
              split nab as {na,nb}.
              let x : Int <- na.
              nb <- (x + x))

new_fuse_ten2_Int_dbl  = \(depth : Int)-> new_ten2_Int_dbl (fuse depth)
new_fuse0_ten2_Int_dbl = new_fuse_ten2_Int_dbl 0
new_fuse1_ten2_Int_dbl = new_fuse_ten2_Int_dbl 1
new_fuse2_ten2_Int_dbl = new_fuse_ten2_Int_dbl 2
new_fuse3_ten2_Int_dbl = new_fuse_ten2_Int_dbl 3
new_fused_ten2_Int_dbl = new_ten2_Int_dbl fused

new_ten2_Int_fwd = new_ten2 (!Int) (?Int)
  (proc(c) c <- 42) (proc(d) let b : Int <- d)
  (proc(nab) fwd 2 (?Int) nab) (fuse 2)

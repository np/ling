replicate_proc =
  \ (A : Type)(n : Int)->
  proc(c : !A -o [!A ^ n])
    split c as {i,os}.
    let x : A <- i.
    split os as [o^n].
    parallel ^ n (o <- x)

replicate_proc_Int_10 = replicate_proc Int 10

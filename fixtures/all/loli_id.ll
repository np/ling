mkfwd =
  \(A : Session)->
   proc(a : A, na : ~A)
    fwd A (a,na)

loli_id :  (A : Session)-> < A -o A >
        = \(A : Session)->
  proc(naa : {~A, A})
    split naa {na,a}.
    @(mkfwd (~A))(na,a)

loli_id_SInt =
  loli_id (!Int)

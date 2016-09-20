zap =
  \(S T : Session)(n : Int)->
  proc(c : [S -o T ^ n] -o [S ^ n] -o [T ^ n])
  split c   as {fs,xos}.
  split xos as {xs,os}.
  split fs  as {f^n}.
  split xs  as {x^n}.
  split os  as [o^n].
  parallel ^ n (
    split f as [fi,fo].
    ( fwd(S)(fi,x)
    | fwd(T)(o,fo)))

{- later on...
zap :  (S T : Session)(n : Int)-> < [S -o T ^ n] -o [S ^ n] -o [T ^ n] >
    = \(S T : Session)(n : Int)->
  proc{{f^n},{{x^n},[o^n]}}
  parallel ^ n
    fwd(S -o T){f, {x,o}}
-}

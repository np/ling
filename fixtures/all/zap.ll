zap =
  \(S T : Session)(n : Int)->
  proc(c : [S -o T ^ n] -o [S ^ n] -o [T ^ n])
  c{fs,xos}
  xos{xs,os}
  fs{f^n}
  xs{x^n}
  os[o^n]
  slice (f,x,o) n as _
    f[fi,fo]
    ( fwd(S)(fi,x)
    | fwd(T)(o,fo))

{- later on...
zap :  (S T : Session)(n : Int)-> < [S -o T ^ n] -o [S ^ n] -o [T ^ n] >
    = \(S T : Session)(n : Int)->
  proc{{f^n},{{x^n},[o^n]}}
  slice (f,x,o) n as _
    fwd(S -o T){f, {x,o}}
-}

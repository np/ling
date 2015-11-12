zap =
  \(S T : Session)(n : Int)->
  proc(c : [S -o T ^ n] -o [S ^ n] -o [T ^ n])
  c{fs,xos}
  xos{xs,os}
  fs{f}
  xs{x}
  os[o]
  slice (f,x,o) n as _
  f[fi,fo]
  ( fwd(S)(fi,x)
  | fwd(T)(o,fo))
{- later on...
  c{{f},{{x},[o]}}
  slice (f,x,o) n as _
  fwd(S -o T){f, {x,o}}
-}

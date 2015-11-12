ap =
  \(S T : Session)->
  proc(c : (S -o T) -o S -o T)
  c{f,xo}
  xo{x,o}
  f[fi,fo]
  ( fwd(S)(fi,x)
  | fwd(T)(o,fo))

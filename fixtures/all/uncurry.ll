uncurry =
  \(S T U : Session)->
  proc(c : (S -o T -o U) -o [S, T] -o U)
-- later on we could replace the 5 lines below by: c{[fx,[fy,fo]],{{x,y},o}}
  c{f,xyo}
  xyo{xy,o}
  xy{x,y}
  f[fx,fyo]
  fyo[fy,fo]
  ( fwd(S)(fx,x)
  | fwd(T)(fy,y)
  | fwd(U)(o,fo))

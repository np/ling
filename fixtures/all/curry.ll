curry =
  \(S T U : Session)->
  proc(c : ([S, T] -o U) -o S -o T -o U)
-- later on we could replace the 5 lines below by: c{[[fx,fy],fo],{x,{y,o}}}
  c{f,xyo}
  xyo{x,yo}
  yo{y,o}
  f[fxy,fo]
  fxy[fx,fy]
  ( fwd(S)(fx,x)
  | fwd(T)(fy,y)
  | fwd(U)(o,fo))



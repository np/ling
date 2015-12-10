curry =
  \(S T U : Session)->
  proc(c : ([S, T] -o U) -o S -o T -o U)
  c{f,xyo}
  xyo{x,yo}
  yo{y,o}
  f[fxy,fo]
  fxy[fx,fy]
  ( fwd(S)(fx,x)
  | fwd(T)(fy,y)
  | fwd(U)(o,fo))

{-
later on...

curry :  (S T U : Session)-> < ([S, T] -o U) -o S -o T -o U >
      = \(S T U : Session)->
  proc{[[fx,fy],fo],{x,{y,o}}}
  ( fwd(S)(fx,x)
  | fwd(T)(fy,y)
  | fwd(U)(o,fo))

or

curry :  (S T U : Session)-> < ([S, T] -o U) -o S -o T -o U >
      = \(S T U : Session)-> proc{[[x:S,y:T],o:U],{x,{y,o}}}
-}

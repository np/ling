data T = `a | `b | `c
rot : (x : T) -> T =
     \(x : T) ->
     case x of
       `a -> `b
       `b -> `c
       `c -> `a

rot2 : (x : T) -> T =
      \(x : T) -> rot (rot x)

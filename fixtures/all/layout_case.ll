data ABC = `a | `b | `c
rot : (x : ABC) -> ABC =
     \(x : ABC) ->
     case x of
       `a -> `b
       `b -> `c
       `c -> `a

rot2 : (x : ABC) -> ABC =
      \(x : ABC) -> rot (rot x)

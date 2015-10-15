feed_send_ten_recv =
  \(p : < [!Int, ?Int] >)
   (f : (x : Int)-> Int)->
  proc()
    new(c : [!Int, ?Int], d : {?Int, !Int})
    ( @p(c)
    | d{i,o}
      recv i (x : Int).
      send o (f x))

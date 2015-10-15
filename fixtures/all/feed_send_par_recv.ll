feed_send_par_recv =
  \(p : < {!Int, ?Int} >)
   (n : Int)->
  proc()
    new(c : {!Int, ?Int}, d : [?Int, !Int])
    ( @p(c)
    | d[i,o]
      ( recv i (x : Int)
      | send o n))

sorter =
 \(n : Int)->
 proc(c : {? Vec Int n, ! Vec Int n})
  c{ci,co}
  recv ci (v : Vec Int n)
  send co (sort n v)

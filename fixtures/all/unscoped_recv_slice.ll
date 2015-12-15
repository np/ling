unscoped_recv_slice = proc(c) (slice (c) 1 as _ (recv c (x : Int))). send c x

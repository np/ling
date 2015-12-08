new_ann_ten_recv = \(ann : Allocation)->
  proc()
    new/ann [c : [!Int, ?Int], d : {?Int, !Int}]
    ( c[co,ci]
      ( send co 42
      | recv ci (y : Int))
    | d{di,do}
      recv di (x : Int).
      send do (x + x))

{- Soon...
new_fuse_ten_recv = \(depth : Int)-> new_ann_ten_recv (fuse depth)
new_fuse1_ten_recv = new_fuse_ten_recv 1
new_fuse2_ten_recv = new_fuse_ten_recv 2
new_fuse3_ten_recv = new_fuse_ten_recv 3
new_fused_ten_recv = new_ann_ten_recv fused
-}

new_fuse1_ten_recv =
  proc()
    new/fuse 1 [c : [!Int, ?Int], d : {?Int, !Int}]
    ( c[co,ci]
      ( send co 42
      | recv ci (y : Int))
    | d{di,do}
      recv di (x : Int).
      send do (x + x))

new_fuse2_ten_recv =
  proc()
    new/fuse 2 [c : [!Int, ?Int], d : {?Int, !Int}]
    ( c[co,ci]
      ( send co 42
      | recv ci (y : Int))
    | d{di,do}
      recv di (x : Int).
      send do (x + x))

new_fuse3_ten_recv =
  proc()
    new/fuse 3 [c : [!Int, ?Int], d : {?Int, !Int}]
    ( c[co,ci]
      ( send co 42
      | recv ci (y : Int))
    | d{di,do}
      recv di (x : Int).
      send do (x + x))

new_fused_ten_recv =
  proc()
    new/fused [c : [!Int, ?Int], d : {?Int, !Int}]
    ( c[co,ci]
      ( send co 42
      | recv ci (y : Int))
    | d{di,do}
      recv di (x : Int).
      send do (x + x))

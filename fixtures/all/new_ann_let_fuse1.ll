new_ann_let_fuse_1 =
  let ann = fuse 1 in
  proc()
    new/ann [c:[],d]
    fwd [] (c,d)

-- The slice command will sequence the `fwd` actions making the `i`
-- channel be read many times.
-- Some sessions are thus considered safe to be repeated, including: ?A
replicate_proc =
  \(A : Type)(n : Int)->
  proc(c : !A -o [!A ^ n])
  c{i,os}
  os[o^n]
  slice (o) n as _
    fwd(!A)(o,i)

-- Here is a version without this trick which relies on the persistency of
-- the variables (not channels)
replicate_proc_alt =
  \(A : Type)(n : Int)->
  proc(c : !A -o [!A ^ n])
  c{i,os}
  recv i (x : A).
  os[o^n]
  slice (o) n as _
    new (j : ?A, k)
    ( fwd(!A)(o,j)
    | send k x)

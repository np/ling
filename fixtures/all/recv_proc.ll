recv_proc_SInt =
  proc(c: ?< !Int >, d: !Int, e: !Int)
    let p : < !Int > <- c.
    @p(d).
    @p(e)

recv_proc_useless =
  proc(c: ?< !Int >, d: !Int, e: !Int)
    e <- 64.
    d <- 42.
    let p : < !Int > <- c

recv_proc_abs_cnt =
  \(S : Session)->
  proc(c: ?< S >, d: S, e: S)
    let p : < S > <- c.
    @p(d).
    @p(e)

recv_proc_loli =
  \(S : Session)->
  proc(a: !< S > -o [ S, S ])
    split a  as {c,de}.
    split de as [d,e].
    let p : < S > <- c.
    ( @p(d) | @p(e) )

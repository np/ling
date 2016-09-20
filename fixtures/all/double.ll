double = proc(a: ?Int, b: !Int)
  let x : Int <- a.
  b <- (x + x)

double_21 = proc(b: !Int)
  new (c :* Int).
  c <- 21.
  @double{c,b}

double_21_seq = proc(b: !Int)
  new [: c : !Int, c' : ?Int :].
  c <- 21.
  @double{c',b}

double_21_fused = proc(b: !Int)
  let x : Int = 21.
  b <- (x + x)

double_21_fused_and_reduced = proc(b: !Int)
  b <- 42

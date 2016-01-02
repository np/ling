fwd_diff1 =
  \ (n: Int)->
  proc(a: [: ?Int ^(1 + n) :], b: [: !Int ^ n :])
    split a [: a0, ai ^ n :].
    split b [: bi ^ n :].
    new (tmp: Int).
    fwd(!Int)(tmp,a0).
    slice (ai,bi) n as _
      (let x: Int <- ai.
       let y: Int <- tmp.
       bi <- (x - y).
       tmp <- x)

recInt
  : (A: (n: Int)-> Type)
    (e: String)
    (z: A 0)
-- TODO using `n` instead of `n1` creates a name capture in fwd_diff.
    (s: (n1: Int)(a: A n1)-> A (1 + n1))
    (n: Int)->
    A n

fwd_diff
  :   (m n: Int)-> < [: ?Int ^(m + n) :], [: !Int ^ n :] >
  = \ (m0 n: Int)->
  recInt (\(m: Int)-> < [: ?Int ^(m + n) :], [: !Int ^ n :] >)
    "m < 0"
    (proc(a: [: ?Int ^ n :], d: [: !Int ^ n :])
       fwd([: ?Int ^ n :])(a,d))
    (\ (m1: Int)(p : < [: ?Int ^(m1 + n) :], [: !Int ^ n :] >)->
       proc(a: [: ?Int ^(1 + (m1 + n)) :], d: [: !Int ^ n :])
         new [: b: [:!Int^(m1 + n):], c :]
         @(fwd_diff1 (m1 + n))(a,b).
         @p(c,d)) m0

fwd_diff1_10 = fwd_diff1 10

tabulate_seq =
  \ (A: Type)
    (f: (i: Int)-> A)
    (n: Int)->
  proc(a: [: !A^n :])
    split a [: a_i^n :].
    slice (a_i) n as i
      a_i <- (f i)

main = proc(c)
  new [: a: [:!Int^10:], b :]
  @(tabulate_seq Int (\(x: Int)-> 10 - x) 10)(a).
  @(fwd_diff 3 7)(b,c)

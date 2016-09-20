Fwd_diff = \ (m n: Int)-> { [: ?Int ^(m + n) :], [: !Int ^ n :] }

fwd_diff1 =
  \ (n: Int)->
  proc(c: Fwd_diff 1 n)
    split c as { a, b }.
    split a as [: a0, ai ^ n :].
    split b as [: bi ^ n :].
    new/alloc (acc :* Int).
    fwd(!Int)(acc,a0).
    split acc as [: acci ^ n :].
    sequence ^ n (
      let x: Int <- ai.
      let y: Int <- acci.
      bi <- (x - y).
      acci <- x
    )

fwd_diff1_10 : < Fwd_diff 1 10 > = fwd_diff1 10

-- Base case: do nothing
fwd_diff0
  :   (n: Int)-> < Fwd_diff 0 n >
  = \ (n: Int)-> proc(c: Fwd_diff 0 n) fwd 2 ([: ?Int ^ n :]) c

fwd_diff_succ =
  \ (ann: Allocation)(n m1: Int)(p: < Fwd_diff m1 n >)->
  proc(ad: Fwd_diff (1 + m1) n)
    split ad as {a: [: ?Int ^(1 + (m1 + n)) :], d: [: !Int ^ n :]}.
    new/ann [: b: [:!Int^(m1 + n):], c :].
    @(fwd_diff1 (m1 + n)){a, b}.
    @p{c, d}

fwd_diff2 :   (ann: Allocation)(n: Int)-> < Fwd_diff 2 n >
          = \ (ann: Allocation)(n: Int)->
  fwd_diff_succ ann n 1 (fwd_diff1 n)
  -- fwd_diff_succ ann n 1 (fwd_diff_succ ann n 0 (fwd_diff0 n))

fwd_diff2_10_alloc : < Fwd_diff 2 10 > = fwd_diff2 alloc 10
-- TODO fwd_diff2_10_fused : < Fwd_diff 2 10 > = fwd_diff2 fused 10

fwd_diff3 :   (ann: Allocation)(n: Int)-> < Fwd_diff 3 n >
          = \ (ann: Allocation)(n: Int)-> fwd_diff_succ ann n 2 (fwd_diff2 ann n)

-- TODO missing definition
recInt
  : (A: (n: Int)-> Type)
    (e: String)
    (z: A 0)
-- TODO using `n` instead of `n1` creates a name capture in fwd_diff.
    (s: (n1: Int)(a: A n1)-> A (1 + n1))
    (n: Int)->
    A n

fwd_diff
  :   (ann: Allocation)(m n: Int)-> < Fwd_diff m n >
  = \ (ann: Allocation)(m0 n: Int)->
  recInt (\(m: Int)-> < Fwd_diff m n >)
    "m < 0"
    (fwd_diff0 n)
    (fwd_diff_succ ann n) m0

tabulate_seq =
  \ (A: Type)
    (f: (i: Int)-> A)
    (n: Int)->
  proc(a: [: !A^n :])
    split a as [: a_i^n :].
    sequence ^ n with i (a_i <- (f i))

main = proc(cc : [: !Int ^ 7 :])
  new/alloc [: a: [: !Int ^ 10 :], bb :].
  @(tabulate_seq Int (\(x: Int)-> 10 - x) 10)(a).
  -- @(fwd_diff 3 7){bb, cc}
  -- TODO fused
  @(fwd_diff3 alloc 7){bb, cc}

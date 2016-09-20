assert 'a' = 'a' : Char
ap =
  \(S T : Session)->
  proc(c : (S -o T) -o S -o T)
  c{f,xo}
  xo{x,o}
  f[fi,fo]
  ( fwd(S)(fi,x)
  | fwd(T)(o,fo))

ap_SInt_SBool = ap (!Int) (!Bool)
app_lambda = (\(x : Int)-> x + x) 21
app_lambda_2 = (\(x : Int)(y : Int)-> x + y) 21 42
app_lambda_let =
  (let x = 21 in \(y : Int)-> x + y) (let notx = 7 in notx + notx + notx)
assert
    `true
  = `true : let B = Bool in
            case `left of { `left -> B, `right -> Int }
assert `false = `false : Bool

assert (\(x:Bool) -> x) = (\(y:Bool) -> y) : ((b:Bool) -> Bool)

assert (not `true) = `false : Bool

assert
    (proc (r : ?Bool.!Bool)
      (recv r (x : Bool) . send r x))
  = (proc (r : ?Bool.!Bool)
      (recv r (y : Bool) . send r y))
  : < ?Bool . !Bool >

assert
    (proc (r : !Bool) (send r (not `true)))
  = (proc (r : !Bool) (send r `false))
  : < !Bool >
another_not : (x : Bool)-> Bool
    = \(x : Bool)-> case x of { `false -> `true, `true -> `false }

pnot = proc(c : ?Bool. !Bool)
  recv c (x : Bool)
  send c (case x of { `false -> `true, `true -> `false })

if : (b : Bool)(A : Type)(t e : A)-> A
   = \(b : Bool)(A : Type)(t e : A)->
      case b of { `true -> t, `false -> e }

If : (b : Bool)(A B : Type)(t : A)(e : B)->
      case b of { `true -> A, `false -> B }
   = \(b : Bool)(A B : Type)(t : A)(e : B)->
      case b of { `true -> t, `false -> e }

{-
Rejected:

if : (b : Bool)(A : Type)(t e : A)->
      case b of { `true -> A, `false -> A }
   = \(b : Bool)(A : Type)(t e : A)->
      case b of { `true -> t, `false -> e }

IF : (b : Bool)(A : (b : Bool)-> Type)(t : A `true)(e : A `false)-> A b
   = \(b : Bool)(A : (b : Bool)-> Type)(t : A `true)(e : A `false)->
      case b of { `true -> t, `false -> e }
-}

assert not `true = `false
assert not `false = `true
assert `false &&  `false = `false
assert `false &&  `true  = `false
assert `true  &&  `false = `false
assert `true  &&  `true  = `true
assert `false ||  `false = `false
assert `false ||  `true  = `true
assert `true  ||  `false = `true
assert `true  ||  `true  = `true
assert `false ==B `false = `true
assert `false ==B `true  = `false
assert `true  ==B `false = `false
assert `true  ==B `true  = `true
assert `false /=B `false = `false
assert `false /=B `true  = `true
assert `true  /=B `false = `true
assert `true  /=B `true  = `false
case_con : case `true of { `true -> Int, `false -> Bool }
         = 1
case_fun_server =
  proc(c : ?(x : Bool). (case x of { `true -> !String, `false -> {!String,!String} }))
  recv c (x : Bool).
  @(case x of
    `true -> proc (c) send c "Hello World!"
    `false ->
       proc (c)
       c{d,e}
       send d "Hello".
       send e "World"
  )(c)
dbl = \(n : Int)-> n + n
case_proto2 =
  \(S : Session)
   (n : Int)
   (p : < S ^ (n + n) >)
   (q : < S ^ (dbl n) >)
   (b : Bool)->
   proc(c)
   @(case b of
       `true  -> p
       `false -> q
   )(c)
My_Int = Int
case_proto
  :  (x : Bool)-> < ?Int >
  = \(x : Bool)-> proc(c : ?Int)
  @(case x of
      `true  -> proc(d : ?Int)    recv d (y : Int)
      `false -> proc(e : ?My_Int) recv e (y : My_Int)
  )(c)
com_new =
 \(S : Session)
  (p : < S  >)
  (q : < ~S >)
  (ann : Allocation)->
  proc()
  new/ann [c : S, d : ~S].
  ( @p(c)
  | @q(d))

com_new_SInt =
  com_new
    (!Int)
    (proc(c' : !Int) c' <- 42)
    (proc(d : ?Int) let x : Int <- d)

com_new_SInt_alloc = com_new_SInt alloc
com_new_SInt_fuse1 = com_new_SInt fuse1

com_new_SInt_RBool =
  com_new
    (!Int.?Bool)
    (proc(c' : !Int.?Bool) c' <- 42. let b : Bool <- c')
    (proc(d : ?Int.!Bool) let x : Int <- d. d <- `true)

com_new_SInt_RBool_alloc = com_new_SInt_RBool alloc
com_new_SInt_RBool_fuse1 = com_new_SInt_RBool fuse1
com_new_SInt_RBool_fuse2 = com_new_SInt_RBool fuse2
com_new_SInt_RBool_fuse3 = com_new_SInt_RBool fuse3
com_new_mk_ten2 =
  let
    mk_tensor2 =
      \ (S0 S1 : Session)
        (p0 : < S0 >)
        (p1 : < S1 >)->
      proc(c : [S0, S1])
        split c as [c0,c1].
        ( @p0(c0)
        | @p1(c1))
  in
  \ (S : Session)
    (p : < S  >)
    (q : < ~S >)
    (ann : Allocation)->
  proc()
    new/ann [c : S, d : ~S].
    @(mk_tensor2 S (~S) p q)[c,d]

com_new_mk_ten2_SInt =
  com_new_mk_ten2 (!Int) (proc(c' : !Int) send c' 42)
                         (proc(d : ?Int) recv d (x : Int))

com_new_mk_ten2_SInt_alloc = com_new_mk_ten2_SInt alloc
com_new_mk_ten2_SInt_fuse1 = com_new_mk_ten2_SInt fuse1
com_new_mk_ten2_SInt_fuse2 = com_new_mk_ten2_SInt fuse2
-- See https://github.com/np/ling/issues/4
com_with_log =
 \(S : Session)
  (p : <      S >)
  (q : <     ~S >)
  (s : < ~Log S >)->
  proc()
  new [c : S,      c' : ~S].
  new [d : ~S,     d' : S].
  new [l : ~Log S, l' : Log S].
  ( @p(c)
  | @q(d)
  | @s(l)
  | fwd S (d',c',l'))
conv_fun =
  \ (A A' B : Type)
    (S : Session)
    (dom : A' -> A)
    (cod : B -> < S >)
    (f   : A -> B)->
  proc(c : !A' -o S)
    c{i,o}
    recv i (p : A')
    @(cod (f (dom p)))(o)
curry =
  \(S T U : Session)->
  proc(c : ([S, T] -o U) -o S -o T -o U)
  c{f,xyo}
  xyo{x,yo}
  yo{y,o}
  f[fxy,fo]
  fxy[fx,fy]
  ( fwd(S)(fx,x)
  | fwd(T)(fy,y)
  | fwd(U)(o,fo))

curry_SInt_SBool_SDouble = curry (!Int) (!Bool) (!Double)

{-
later on...

curry :  (S T U : Session)-> < ([S, T] -o U) -o S -o T -o U >
      = \(S T U : Session)->
  proc{[[fx,fy],fo],{x,{y,o}}}
  ( fwd(S)(fx,x)
  | fwd(T)(fy,y)
  | fwd(U)(o,fo))

or

curry :  (S T U : Session)-> < ([S, T] -o U) -o S -o T -o U >
      = \(S T U : Session)-> proc{[[x:S,y:T],o:U],{x,{y,o}}}
-}
cutEmptyParTensor = proc() new [c : {}, d : []]. (c{} | d[])
cut_par_cut = proc()
  ( new [c  : !Int, d  : ?Int]. ( send c  1 | recv d  (x  : Int) )
  | new [c' : !Int, d' : ?Int]. ( send c' 1 | recv d' (x' : Int) )
  )

cutSendRecv = proc() new [c : !Int, d : ?Int]. ( send c 1 | recv d (x : Int) )
cut_send_recv_recv_send_with_log =
  proc(logc : !String.!String, logd : !String.!String)
  new [c : !Int.?Int, d : ?Int.!Int].
  ( send logd "recv d".
    recv d (y : Int).
    send logd "send d 2".
    send d 2
  | send logc "send c 1".
    send c 1.
    send logc "recv c".
    recv c (x : Int))
cut_send_recv_recv_send_with_log_prll =
  proc(logc : !String.!String, logd : !String.!String)
  new [c : !Int.?Int, d : ?Int.!Int].
  ( ( send logd "recv d"
    | recv d (y : Int)).
    ( send logd "send d 2"
    | send d 2)
  | ( send logc "send c 1"
    | send c 1).
    ( send logc "recv c"
    | recv c (x : Int)))
dep_fun_server =
  \(A : Type)
   (B : (x : A)-> Type)
   (f : (x : A)-> B x)->
   proc(c : ?(x : A). !B x)
   recv c (x : A).
   send c (f x)
div_mod_server_cont = proc(c : ?Int.?Int.!Int.!Int)
  recv c (m : Int).
  recv c (n : Int).
  send c (m / n).
  send c (m % n)
div_mod_server_explicit_prll = proc(rm : ?Int, rn : ?Int, sdiv : !Int, smod : !Int)
  ( recv rn (n : Int)
  | recv rm (m : Int)).
  ( send sdiv (m / n)
  | send smod (m % n))
div_mod_server_par2_ten2_ten2 = proc(r : [?Int, ?Int], s : [!Int, !Int])
  r[rm,rn]
  s[sdiv,smod]
  ( recv rm (m : Int)
  | recv rn (n : Int)).
  ( send sdiv (m / n)
  | send smod (m % n))
div_mod_server_par4 = proc(c : {?Int, ?Int, !Int, !Int})
  c{rm,rn,sdiv,smod}
  recv rm (m : Int).
  recv rn (n : Int).
  send sdiv (m / n).
  send smod (m % n)
div_mod_server_seq2_ten2_ten2 = proc(c : [: [?Int, ?Int], [!Int, !Int] :])
  c[:r,s:]
  r[rm,rn]
  s[sdiv,smod]
  ( recv rm (m : Int)
  | recv rn (n : Int)).
  ( send sdiv (m / n)
  | send smod (m % n))
div_mod_server_seq4 = proc(c : [: ?Int, ?Int, !Int, !Int :])
  c[:rm,rn,sdiv,smod:]
  recv rm (m : Int).
  recv rn (n : Int).
  send sdiv (m / n).
  send smod (m % n)
div_mod_server_simple = proc(rm : ?Int, rn : ?Int, sdiv : !Int, smod : !Int)
  recv rm (m : Int).
  recv rn (n : Int).
  send sdiv (m / n).
  send smod (m % n)
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
another_dual = \(S : Session)-> ~S
dual_dual =
  \(S : Session)
   (p : < S >)->
   proc(c : ~another_dual S)
   @p(c)
assert 1 + 3 = 2 + 2 : Int
my_zero = 0
assert ((S T : Session)-> < S ^ 5, T ^(0 + my_zero) >)
     = ((S T : Session)-> < S ^ 2, T ^ 0, S, S ^ 1, S >)
     : Type
assert ((S : Session)(m n : Int)-> < S ^(m + n)   >)
     = ((S : Session)(m n : Int)-> < S ^ m, S ^ n >)
     : Type
fake_div_mod_server_ten2 = proc(r : [?Int, ?Int], s : [!Int, !Int])
  r[rm,rn]
  s[sdiv,smod]
  ( send sdiv 42
  | send smod 21).
  ( recv rm (m : Int)
  | recv rn (n : Int))
feed_fwd_send_then_recv =
  \(I O : Type)
   (i : I)
   (f : (x : I)-> O)
   (p : < Fwd 2 (!I.?O) >)->
  proc()
   new [a : Fwd 2 (!I.?O), b : [?I.!O, !I.?O]].
   ( @p(a)
   | b[c,d]
     ( recv c (x : I).
       send c (f x)
     | send d i.
       recv d (o : O)))

feed_fwd_send_then_recv_Int_String_42_showInt =
  feed_fwd_send_then_recv Int String 42 showInt
  (proc(c) fwd 2 (!Int.?String) c)
feed_recv =
  \(p : < ?Int >)
   (i : Int)->
  proc()
    new [c : ?Int,d].
    ( @p(c) | send d i )
feed_send =
  \(p : < !Int >)->
  proc()
    new [c : !Int,d].
    ( @p(c) | recv d (x : Int) )
feed_send_par_recv =
  \(p : < {!Int, ?Int} >)
   (n : Int)->
  proc()
    new [c : {!Int, ?Int}, d : [?Int, !Int]].
    ( @p(c)
    | d[i,o]
      ( recv i (x : Int)
      | send o n))
feed_send_ten_recv =
  \(p : < [!Int, ?Int] >)
   (f : (x : Int)-> Int)->
  proc()
    new [c : [!Int, ?Int], d : {?Int, !Int}].
    ( @p(c)
    | d{i,o}
      recv i (x : Int).
      send o (f x))
feed_send_then_recv =
  \(p : < !Int. ?Int >)
   (f : (x : Int)-> Int)->
  proc()
    new [c : !Int. ?Int,d].
    ( @p(c)
    | recv d (x : Int). send d (f x) )
flexible_telescope
  :  (A B : Type)(x y : A)(z t : B)-> Int
  = \(A B : Type)(x y : A)(z t : B)-> 42
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
fun1_to_proc_ord =
  \(I O : Type)
   (f : (x : I) -> O)->
  proc(c : [: ?I, !O :])
  c[: i, o :]
  recv i (x : I).
  send o (f x)
fun1_to_proc_par2 =
  \(I O : Type)
   (f : (x : I) -> O)->
  proc(i : ?I, o : !O)
  recv i (x : I).
  send o (f x)
fun1_to_proc_seq =
  \(I O : Type)
   (f : (x : I) -> O)->
  proc(c : ?I. !O)
  recv c (x : I).
  send c (f x)
fwd0_snd0 = proc(c : Fwd 0 (!Empty)) fwd 0 (!Empty) c
fwd1_par2_rcv =
  proc(c : Fwd 1 {?Int,?Bool})
  fwd 1 {?Int,?Bool} c
fwd1_rcv = proc(c : Fwd 1 (?Int)) fwd 1 (?Int) c
fwd1_seq2_rcv =
  proc(c : Fwd 1 [:?Int,?Bool:])
  fwd 1 [:?Int,?Bool:] c
fwd1_ten2_rcv =
  proc(c : Fwd 1 [?Int,?Bool])
  fwd 1 [?Int,?Bool] c
fwd2_par2_ten2 = proc(c : Fwd 2 {?Int,!Int.?Int}) fwd 2 {?Int,!Int.?Int} c
fwd3_par2_ten2_ten2 = proc(c : Fwd 3 {?Int,!Int.?Int})
  fwd 3 {?Int,!Int.?Int} c
fwd3_seq2_seq2_seq2 = proc(c : Fwd 3 [: ?Int, !Int.?Int :])
  fwd 3 [: ?Int,!Int.?Int :] c
fwd_par0_ten0 = proc(i : {}, o : []) fwd{}(i,o)
fwd_par2_ten2_expanded =
  proc (i : {?Int, !Int.?Int},o : [!Int, ?Int.!Int])
  o [o0, o1]
  i {i0, i1}
  ( recv i0 (xi0 : Int).
    send o0 xi0
  | recv o1 (xo1 : Int).
    send i1 xo1.
    recv i1 (xi1 : Int).
    send o1 xi1 )
fwd_par2_ten2 = proc(i : {?Int,!Int.?Int}, o : [!Int,?Int.!Int]) fwd{?Int,!Int.?Int}(i,o)
fwd_par2_ten2_ten2 =
  proc( i : {?Int,!Int.?Int}
      , o : [!Int,?Int.!Int]
      , l : {!Int,!Int.!Int}
      )
  fwd {?Int,!Int.?Int}(i,o,l)
fwd_par2_ten2_ten2_ten2 =
  proc( i : {?Int,!Int.?Int}
      , o : [!Int,?Int.!Int]
      , l : {!Int,!Int.!Int}
      , m : {!Int,!Int.!Int}
      )
  fwd{?Int,!Int.?Int}(i,o,l,m)
fwd_parN_tenN = \(n : Int)-> proc(i : {?Int ^ n}, o : [!Int ^ n]) fwd{?Int ^ n}(i,o)

fwd_par10_ten10 = fwd_parN_tenN 10
fwd_send_recv = proc(i : ?Int, o : !Int) fwd(?Int)(i,o)
fwd_send_recv_recv_auto = proc(c : !Int.?Int.?Int, d : ?Int.!Int.!Int)
  fwd(!Int.?Int.?Int)(c,d)
fwd_send_recv_recv_manually = proc(c : !Int.?Int.?Int, d : ?Int.!Int.!Int)
  recv d (x : Int).
  send c x.
  recv c (y : Int).
  send d y.
  recv c (z : Int).
  send d z
fwd_send_recv_recv_send = proc(i : ?Int. !Int, o : !Int. ?Int) fwd(?Int.!Int)(i,o)
fwd_send_recv_recv_with_listener_auto =
  proc(c : !Int.?Int.?Int,
       d : ?Int.!Int.!Int,
       e : !Int.!Int.!Int)
  fwd(!Int.?Int.?Int)(c,d,e)
fwd_send_recv_recv_with_listener_manually =
  proc(c : !Int.?Int.?Int,
       d : ?Int.!Int.!Int,
       e : !Int.!Int.!Int)
  recv d (x : Int).
  ( send c x
  | send e x).
  recv c (y : Int).
  ( send d y
  | send e y).
  recv c (z : Int).
  ( send d z
  | send e z)
fwd_seq2_seq2_seq2 =
  proc( i : [: ?Int, !Int.?Int :]
      , o : [: !Int, ?Int.!Int :]
      , l : [: !Int, !Int.!Int :]
      )
  fwd [: ?Int,!Int.?Int :](i,o,l)
fwd_ten2_par2 = proc(i : [?Int,!Int.?Int], o : {!Int,?Int.!Int}) fwd[?Int,!Int.?Int](i,o)
split_nested_seq_core =
  \(A B C D : Session)->
   proc(i : [: ~A, ~B, ~C, ~D :], o : [: [: A, B :], [: C, D :] :])
    i[:na,nb,nc,nd:]
    o[:ab,cd:]
    ab[:a,b:]
    cd[:c,d:]
    fwd A (a,na).
    fwd B (b,nb).
    fwd C (c,nc).
    fwd D (d,nd)

group_nested_seq :
  (A B C D : Session)->
  < [: [: A, B :], [: C, D :] :] -o [: A, B, C, D :] > =
  \(A B C D : Session)->
   proc(c : {[: [: ~A, ~B :], [: ~C, ~D :] :], [: A, B, C, D :]})
     c{i,o}
     @(split_nested_seq_core (~A) (~B) (~C) (~D))(o,i)

group_nested_seq_SInt_SDouble_SBool_SString =
  group_nested_seq (!Int) (!Double) (!Bool) (!String)
idProc = proc(c : ?Int, d : !Int)
  let y : Int <- c.
  d <- (id Int y)
idType = \(idTypeA : Type)-> idTypeA
idTypeA : Type
idTypeX : idType idTypeA
assert 42 = let x = 42 in x
i42 : Int = 42
one : Int = 1

suc : (x : Int) -> Int = _+_ one

doubleInt : (x : Int)-> Int = \(x : Int)-> x + x
data ABC = `a | `b | `c
rot : (x : ABC) -> ABC =
     \(x : ABC) ->
     case x of
       `a -> `b
       `b -> `c
       `c -> `a

rot2 : (x : ABC) -> ABC =
      \(x : ABC) -> rot (rot x)
let42ann =
  let x : Int = 42 in
  x + x
let42 = let x = 42 in x + x
let_example =
   let T = Int in
   let f = _+_ in
   proc(c : ?T.!T)
   recv c (x : T).
   let y = (f x x).
   send c y
let_in_proc_for_session = proc(c : ?Int)
  let A = Int. let x : A <- c
let_let =
  let x = 1 in
  let y = x in
  y
let_order =
  let x = 1 in
  let y = 2 in
  x + y
let_order_proc = proc(c : !Int)
  let x = 1.
  let y = 2.
  c <- (x + y)
letrecv_ann = proc(c : ?Int.!Int)
  recv c (x : Int).
  let y : Int = (x + x).
  send c y
letrecv = proc(c : ?Int.!Int)
  recv c (x : Int).
  let y = (x + x).
  send c y
letsession =
  let f = \(S0 : Session)->
            let S1 = {S0,S0} in
            let S2 = {S1,S1} in
            let S3 = {S2,S2} in
            let S4 = {S3,S3} in
            let S5 = {S4,S4} in
            let S6 = {S5,S5} in
            let S7 = {S6,S6} in
            S7
  in
  proc(c)
  fwd 2 (f (?Int)) c
lettype
  : (P : (A B : Type)-> Type)
    (p : (A : Type)-> P A A)
    (A : Type)->
    P (P (P (P A A) (P A A)) (P (P A A) (P A A)))
      (P (P (P A A) (P A A)) (P (P A A) (P A A)))
  =
   \(P : (A B : Type)-> Type)
    (p : (A : Type)-> P A A)
    (A : Type)->
    let B = P A A in
    let C = P B B in
    let D = P C C in
    p D
assert 1 = let f = \(x : Int)-> x in f (f 1) : Int
showMult = \(m n : Int) ->
  (showInt m) ++S " * " ++S (showInt n) ++S " = " ++S showInt (m * n)

showDiv = \(m n : Double) ->
  (showDouble m) ++S " / " ++S (showDouble n) ++S " = " ++S showDouble (m /D n)

my42 : String = showMult 2 21

my3_14 : String = showDiv 6.28 2.0

myNewline : Char = '\n'
mkfwd =
  \(A : Session)->
   proc(a : A, na : ~A)
    fwd A (a,na)

loli_id :  (A : Session)-> < A -o A >
        = \(A : Session)->
  proc(naa : {~A, A})
    split naa {na,a}.
    @(mkfwd (~A))(na,a)

loli_id_SInt =
  loli_id (!Int)
zipWith =
  \(A B C : Type)
   (f : (a : A)(b : B)-> C)
   (n : Int)->
  proc(cas : [: ?A ^ n :], cbs : [: ?B ^ n :], ccs : [: !C ^ n :])
    split cas[:ca^n:]
    split cbs[:cb^n:]
    split ccs[:cc^n:]
    sequence ^ n (
      -- could be parallel
      let a : A <- ca.
      let b : B <- cb.
      cc <- (f a b)
    )

{-
zipWith =
  \(A B C : Type)
   (f : (a : A)(b : B)-> C)
   (n : Int)->
  proc([: ca : ?A ^ n :], [: cb : ?B ^ n :], [: cc : !C ^ n :])
    sequence ^ n as _
      cc <- (f (<- ca) (<- cb))
-}

zip_multD = zipWith Double Double Double _*D_

{-
zip_multI = zipWith Int Int Int _*_

_==D_ : (x y : Double)-> Bool

zip_multI = zipWith Double Double Bool _==D_
-}

foldl =
  \(A B : Type)
   (f : (acc : B)(a : A)-> B)
   (init : B)
   (n : Int)->
  proc(ca : [: ?A ^ n :], cr : !B)
  new/alloc (acc :* B).
  acc <- init.
  split acc [: acci ^ n, accn :]
  split ca[: ai^n :].
  sequence ^ n (
     ( let a : A <- ai
     | let b : B <- acci).
     acci <- (f b a)
  ).
  fwd(?B)(accn, cr)

sumD : (n : Int)-> < [: ?Double ^ n :], !Double >
     = foldl Double Double _+D_ 0.0

dotproduct = \(n : Int)(ann : Allocation)->
  proc(as' : [: ?Double ^ n :], bs : [: ?Double ^ n :], o : !Double)
    new/ann [: cs : [: !Double ^ n :], ds :].
    @(zip_multD n){as', bs, cs}.
    @(sumD n){ds, o}

dotproduct_4_alloc = dotproduct 4 alloc
dotproduct_4_fused = dotproduct 4 fused

-- There should be a proof that i is in 0..n-1
ix : (A : Type)(n : Int)(v : Vec A n)(i : Int) -> A

{- conventions:
  m: number of rows
  n: number of cols
  i: row index (valued in 0..m-1)
  j: col index (valued in 0..n-1)

  each row is a vector of n elements
  each col is a vector of m elements

  m_{i,j} is located at position ((i * n) + j) in m

  Use (/ n) to get back i
  Use (% n) to get back j
-}

row = \(A : Type)(m n : Int)(a : Vec A (m * n))(i : Int)-> proc(v : [: !A^n :])
  split v [: v_i^n :].
  sequence ^ n with j (
    v_i <- (ix A (m * n) a ((i * n) + j))
  )

col = \(A : Type)(m n : Int)(a : Vec A (m * n))(j : Int)-> proc(v : [: !A^m :])
  split v [: v_j^m :].
  sequence ^ m with i (
    v_j <- (ix A (m * n) a ((i * n) + j))
  )

matmult = \(m n p : Int)(ann0 ann1 ann2 : Allocation)->
           proc(a : ?Vec Double (m * n),
                b : ?Vec Double (n * p),
                c : [: !Double^(m * p) :])
  let a' : Vec Double (m * n) <- a.
  let b' : Vec Double (n * p) <- b.
  split c as [: c_i_j^(m * p) :].
  sequence ^ (m * p) with ij (
    new/ann0 [: u : [: !Double^n :], u' :].
    @(row Double m n a' (ij / n))(u).
    new/ann1 [: v : [: !Double^n :], v' :].
    @(col Double n p b' (ij % n))(v).
    -- Working around a bug name-binding bug...
    let nn = n.
    @(dotproduct nn ann2){u',v',c_i_j}
  )

matmult_4_alloc = matmult 4 4 4 alloc alloc alloc
-- TODO turning any fusion here is broken so far.
-- matmult_4_fused = matmult 4 4 4 alloc alloc fused
-- Should be renamed merge_ParSort_seq_recv
merger =
 \(m n : Int)->
 proc( c0 : [! Vec Int m, ? Vec Int m]
     , c1 : [! Vec Int n, ? Vec Int n]
     , ci : ? Vec Int (m + n)
     , co : ! Vec Int (m + n)
     )
  c0[c0i,c0o]
  c1[c1i,c1o]
  recv ci (vi : Vec Int (m + n))
  ( send c0i (take Int m n vi)
  | send c1i (drop Int m n vi)
  | recv c0o (v0 : Vec Int m)
    recv c1o (v1 : Vec Int n)
    send co  (merge m n v0 v1)
  )
merger_loli_Sort =
 \(m n : Int)->
 proc( c : {DotSort Int m, DotSort Int n} -o DotSort Int (m + n) )
  c{c01,d}
  c01[c0,c1]
  recv d (vi : Vec Int (m + n)).
  ( send c0 (take Int m n vi)
  | send c1 (drop Int m n vi)).
  ( recv c0 (v0 : Vec Int m)
  | recv c1 (v1 : Vec Int n)).
  send d (merge m n v0 v1)
merger_nstSort_prll =
 \(m n : Int)->
 proc( c0 : ~DotSort Int m
     , c1 : ~DotSort Int n
     , c  : DotSort Int (m + n)
     )
  recv c (vi : Vec Int (m + n)).
  ( send c0 (take Int m n vi)
  | send c1 (drop Int m n vi)).
  ( recv c0 (v0 : Vec Int m)
  | recv c1 (v1 : Vec Int n)).
  send c (merge m n v0 v1)
merger_nstSort_prll_v2 =
 \(m n : Int)->
 proc( c : [~DotSort Int m, ~DotSort Int n]
     , d : DotSort Int (m + n)
     )
  c[c0,c1]
  recv d (vi : Vec Int (m + n)).
  ( send c0 (take Int m n vi)
  | send c1 (drop Int m n vi)).
  ( recv c0 (v0 : Vec Int m)
  | recv c1 (v1 : Vec Int n)).
  send d (merge m n v0 v1)
merger_ParSort_full_prll =
 \(m n : Int)->
 proc( c0 : ~ParSort Int m
     , c1 : ~ParSort Int n
     , c  : ParSort Int (m + n)
     )
  c0[c0i,c0o]
  c1[c1i,c1o]
  c{ci,co}
  recv ci (vi : Vec Int (m + n)).
  ( send c0i (take Int m n vi)
  | send c1i (drop Int m n vi)
  | ( recv c0o (v0 : Vec Int m)
    | recv c1o (v1 : Vec Int n)).
    send co (merge m n v0 v1))
merger_seq_inferred =
 \(m n : Int)->
 proc(c0,c1,ci,co)
  recv ci (vi : Vec Int (m + n)).
  send c0 (take Int m n vi).
  send c1 (drop Int m n vi).
  recv c0 (v0 : Vec Int m).
  recv c1 (v1 : Vec Int n).
  send co (merge m n v0 v1)
merger_seq =
 \(m n : Int)->
 proc( c0 : ! Vec Int m. ? Vec Int m
     , c1 : ! Vec Int n. ? Vec Int n
     , ci : ? Vec Int (m + n)
     , co : ! Vec Int (m + n)
     )
  recv ci (vi : Vec Int (m + n)).
  send c0 (take Int m n vi).
  send c1 (drop Int m n vi).
  recv c0 (v0 : Vec Int m).
  recv c1 (v1 : Vec Int n).
  send co (merge m n v0 v1)
merger_seq_Sort =
 \(m n : Int)->
 proc(c : [DotSort Int m, DotSort Int n] -o DotSort Int (m + n))
  c{d,io} d{d0,d1}
  recv io (vi : Vec Int (m + n)).
  send d0 (take Int m n vi).
  send d1 (drop Int m n vi).
  recv d0 (v0 : Vec Int m).
  recv d1 (v1 : Vec Int n).
  send io (merge m n v0 v1)
merger_seqential_ten2_loli_Sort =
 \(m n : Int)->
 proc( c : [DotSort Int m, DotSort Int n] -o DotSort Int (m + n) )
  c{c01,d}
  c01{c0,c1}
  recv d (vi : Vec Int (m + n)).
  send c0 (take Int m n vi).
  send c1 (drop Int m n vi).
  recv c0 (v0 : Vec Int m).
  recv c1 (v1 : Vec Int n).
  send d (merge m n v0 v1)
merger_ten2_loli_Sort =
 \(m n : Int)->
 proc( c : [DotSort Int m, DotSort Int n] -o DotSort Int (m + n) )
  c{c01,d}
  c01{c0,c1}
  recv d (vi : Vec Int (m + n)).
  ( send c0 (take Int m n vi)
  | send c1 (drop Int m n vi)).
  ( recv c0 (v0 : Vec Int m)
  | recv c1 (v1 : Vec Int n)).
  send d (merge m n v0 v1)
mk_new_ann =
  \(ann : Allocation)
   (S : Session)
   (p : < S  >)
   (q : < ~S >)->
  proc()
    new/ann [c : S, d : ~S]
    ( @p(c)
    | @q(d))
mk_new_seq =
  \(ann : Allocation)
   (S : Session)
   (p : <  Log S >)
   (q : < ~Log S >)->
  proc()
    new/ann [: c : Log S, d :]
    @p(c).
    @q(d)
mk_par2_LR =
  \ (S0 S1 : Session)
    (p0 : < S0 >)
    (p1 : < S1 >)->
  proc(c : {S0, S1})
    c{c0,c1}
    @p0(c0).
    @p1(c1)
mk_par2_prll =
  \ (S0 S1 : Session)
    (p0 : < S0 >)
    (p1 : < S1 >)->
  proc(c : {S0, S1})
    c{c0,c1}
    ( @p0(c0)
    | @p1(c1))
mk_par2_RL =
  \ (S0 S1 : Session)
    (p0 : < S0 >)
    (p1 : < S1 >)->
  proc(c : {S0, S1})
    c{c0,c1}
    @p1(c1).
    @p0(c0)
mkrecv = \(A : Type)-> proc(a : ?A) let x : A <- a

mkrecvInt = mkrecv Int
mksend = \(A : Type)(x : A)-> proc(a : !A) a <- x

mksendInt42 = mksend Int 42
mk_seq2 =
  \ (S0 S1 : Session)
    (p0 : < S0 >)
    (p1 : < S1 >)->
  proc(c : [: S0, S1 :])
    c[: c0, c1 :]
    @p0(c0).
    @p1(c1)
-- a needlessly complicated version of mk_tensor2
-- (should be convertible with it)
mk_ten2_2new_2fwd =
 \(S0 S1 : Session)
  (p0 : < S0 >)
  (p1 : < S1 >)->
  proc(c : [S0, S1])
  c[c0,c1]
  new [d0 : ~S0, e0 : S0].
  new [d1 : ~S1, e1 : S1].
  ( @p0(e0)
  | fwd S0 (c0, d0)
  | @p1(e1)
  | fwd S1 (c1, d1))

{-
mk_ten2_2new_2fwd_SInt_SDouble =
  let mk_send = \(A : Type)(x : A)-> proc(c : !A) send c x in
  mk_ten2_2new_2fwd (!Int) (!Double)
    (mk_send Int 42) (mk_send Double 3.14)

mk_ten2_2new_2fwd_SInt_SDouble =
  mk_ten2_2new_2fwd (!Int) (!Double)
    (proc(ci : !Int) send ci 42) (proc(cd : !Double) send cd 3.14)
-}
mk_tensor2 =
  \ (S0 S1 : Session)
    (p0 : < S0 >)
    (p1 : < S1 >)->
  proc(c : [S0, S1])
    c[c0,c1]
    ( @p0(c0)
    | @p1(c1))
assert ?(A B : Type)(C : Type)
     = ?(A : Type). ?(B : Type). ?(C : Type)
     : Session
my_dual = \(S : Session)-> ~S

test_my_dual = proc(c : my_dual (!Int))
  recv c (x : Int)
my_loli = \(S T : Session) -> {~S,T}

test_my_loli =
 \(A : Type)->
  proc(c : my_loli (!A) (!A))
  c{i,o}
  recv i (x : A).
  send o x
new_alloc = proc(c : !Int)
  new/alloc [d : !Int, e]
  ( send d 1
  | fwd(!Int)(c,e))
new_fuse1_recv_send_send_recv = proc()
  new/fuse 1 [d : ?Int.!Int, c : !Int.?Int]
  ( send c 1
    recv c (x : Int)
  | recv d (y : Int)
    send d 2
  )
new_seq_par_par =
  proc()
  new/alloc [: cd: {!Int,!Bool}, ef: {?Int,?Bool} :].
  split cd {c,d}.
  split ef {e,f}.
  c <- 1.
  d <- `true.
  let b : Bool <- f.
  let i : Int  <- e
new_ten2 =
  \(A B : Session)
   (pA  : < A >)
   (pB  : < B >)
   (pC  : < {~A,~B} >)
   (ann : Allocation)->
  proc()
    new/ann [ab : [A,B], nab : {~A,~B}].
    ( split ab as [a,b].
      ( @(pA)(a)
      | @(pB)(b))
    | @(pC)(nab))

new_ten2_Int_dbl =
  new_ten2 (!Int) (?Int) (proc(c) c <- 42) (proc(d) let b : Int <- d)
           (proc(nab)
              split nab as {na,nb}.
              let x : Int <- na.
              nb <- (x + x))

new_fuse_ten2_Int_dbl  = \(depth : Int)-> new_ten2_Int_dbl (fuse depth)
new_fuse0_ten2_Int_dbl = new_fuse_ten2_Int_dbl 0
new_fuse1_ten2_Int_dbl = new_fuse_ten2_Int_dbl 1
new_fuse2_ten2_Int_dbl = new_fuse_ten2_Int_dbl 2
new_fuse3_ten2_Int_dbl = new_fuse_ten2_Int_dbl 3
new_fused_ten2_Int_dbl = new_ten2_Int_dbl fused

new_ten2_Int_fwd = new_ten2 (!Int) (?Int)
  (proc(c) c <- 42) (proc(d) let b : Int <- d)
  (proc(nab) fwd 2 (?Int) nab) (fuse 2)
-- Requires a mix
no_dead_lock_new_new = proc()
  new [c : ?Int, d].
  new [e : ?Int, f].
  ( recv c (x : Int).
    send f x
  | send d 5
  | recv e (y : Int))
no_dead_lock_new_new_seq = proc()
  new [: d : !Int, c :]
  new [: f : !Int, e :]
  send d 5.
  recv c (x : Int).
  send f x.
  recv e (y : Int)
-- Requires a mix
no_dead_lock_new_new_v2 = proc()
  new [c : ?Int, d].
  new [e : ?Int, f].
  ( send d 5
  | ( recv c (x : Int).
      send f x
    | recv e (y : Int)))
non_dependent_function_type : Int -> Int = \(x : Int) -> x + 1
assert (A : Type)(a0 : A)(B : (a : A)-> Type)-> (B a0 -> Type)
     = (A : Type)(a0 : A)(B : (a : A)-> Type)-> ((b : B a0) -> Type)
     : Type
assert (A : Type)(a0 : A)(B : (a : A)-> Type)-> < ?     B a0  >
     = (A : Type)(a0 : A)(B : (a : A)-> Type)-> < ?(b : B a0) >
     : Type
some_type : Type = Int , some_value : some_type = 42
Oplus' = \(SL SR : Session)-> !(b : LR). (case b of { `left -> SL, `right -> SR })

leftOplus =
  \(SL SR : Session)(p : < SL >)->
    proc(c)
    c : Oplus' SL SR <- `left.
    @p(c)

rightOplus =
  \(SL SR : Session)(p : < SR >)->
    proc(c)
    c : Oplus' SL SR <- `right.
    @p(c)

oplus' =
  \(SL SR : Session)
   (b : LR)
   (p : < case b of { `left -> SL, `right -> SR } >)->
    proc(c)
    c : Oplus' SL SR <- b.
    @p(c)

assert leftOplus
     = \(SL SR : Session)-> oplus' SL SR `left
     : (SL SR : Session)(p : < SL >)-> < Oplus' SL SR >

assert rightOplus
     = \(SL SR : Session)-> oplus' SL SR `right
     : (SL SR : Session)(p : < SR >)-> < Oplus' SL SR >
par0 = proc(c : {}) c{}
par1 = proc(c : {!Int}) c{d} send d 42
par2 = proc(c : {!Int,?Int}) c{d,e} recv e (x : Int) send d x
par2mix = proc(c : {!Int,?Int}) c{d,e}(recv e (x : Int) | send d 42)
par4_seq_send3 = proc(a : {[:!Int,!Int:],!Int,!Int,!Int})
  a{b,e,f,g} b[:c,d:] send e 1 send c 2 send f 3 send d 4 send g 5
parallel_assoc_2tensor2_left = proc(cde : [[!Int, !Int], !Int])
  cde[cd,e]
  cd[c,d]
  ( send c 1
  | send d 2
  | send e 3
  )
parallel_assoc_2tensor2_right = proc(cde : [[!Int, !Int], !Int])
  cde[cd,e]
  ( cd[c,d] ( send c 1 | send d 2 )
  | send e 3
  )
parallel_assoc_flat = proc(c : !Int, d : !Int, e : !Int)
  ( send c 1
  | send d 2
  | send e 3
  )
parallel_assoc_left = proc(c : !Int, d : !Int, e : !Int)
  ( ( send c 1 | send d 2 )
  | send e 3
  )
parallel_assoc_right = proc(c : !Int, d : !Int, e : !Int)
  ( send c 1
  | ( send d 2 | send e 3 )
  )
parallel_assoc_tensor3_flat = proc(cde : [!Int, !Int, !Int])
  cde[c,d,e]
  ( send c 1
  | send d 2
  | send e 3
  )
parallel_assoc_tensor3_left = proc(cde : [!Int, !Int, !Int])
  cde[c,d,e]
  ( send c 1
  | ( send d 2 | send e 3 )
  )
parallel_assoc_tensor3_right = proc(cde : [!Int, !Int, !Int])
  cde[c,d,e]
  ( ( send c 1 | send d 2 )
  | send e 3
  )
parallel_tensor4_flat = proc(cd : [!Int,!Int], ef : [!Int,!Int])
  cd[c,d]
  ef[e,f]
  ( send c 1
  | send e 2
  | send d 3
  | send f 4
  )
-- Needs mix
-- [c,d],[e,f] <mix> [c,d,e,f] <split> [c,e],[d,f] <split/split> [c],[e] and [d],[f]
parallel_tensor4_v0 = proc(cd : [!Int,!Int], ef : [!Int,!Int])
  cd[c,d]
  ef[e,f]
  ( ( send c 1 | send e 2 )
  | ( send d 3 | send f 4 )
  )
par_comm =
 \(A B : Session)->
 proc(c : {A,B} -o {B,A})
  c{i,o}
  i[na,nb]
  o{b,a}
  (fwd(A)(a,na) | fwd(B)(b,nb))
par_loli_ten_send =
 \(S T : Type)->
 proc(c : {!S,!T} -o [!S,!T])
  c{i,o}
  i[rs,rt]
  o[ss,st]
  ( recv rs (vs : S)
  | recv rt (vt : T)).
  ( send ss vs
  | send st vt)
par_loli_ten_send_v2 =
 \(S T : Type)->
 proc(c : {!S,!T} -o [!S,!T])
  c{i,o}
  i[rs,rt]
  ( recv rs (vs : S)
  | recv rt (vt : T)).
  o[ss,st]
  ( send ss vs
  | send st vt)

{-
par_loli_ten_send_v3
  :  (S T : Type)-> <{!S,!T} -o [!S,!T]>
  = \(S T : Type)->
 proc{[rs,rt],[ss,st]}
  ( let vs : S = <-rs
  | let vt : T = <-rt).
  ( ss <- vs
  | st <- vt)
-}
par_pat = proc(d : !Int, e : ?Int)
  @(proc (f) fwd 2 (!Int) f){d,e}
par_seq_back = proc(a : {[:!Int,!Int:],!Int})
  a{b,e} b[:c,d:] send c 2 send d 3 send e 1
par_seq_front = proc(a : {[:!Int,!Int:],!Int})
  a{b,e} b[:c,d:] send e 1 send c 2 send d 3
-- should be infix _-:_
seqi = \(S0 S1 : Session)-> [: ~S0, S1 :]

par_seqi_ten_send =
 \(A B : Type)->
 proc(c : seqi {!A,!B} [!A,!B])
  c[:i,o:]
  i[rs,rt]
  o[ss,st]
  ( recv rs (vs : A)
  | recv rt (vt : B)).
  ( send ss vs
  | send st vt)
par_seq_middle = proc(a : {[:!Int,!Int:],!Int})
  a{b,e} b[:c,d:] send c 2 send e 1 send d 3
par_seq_send3 = proc(a : {[:!Int,!Int:],!Int.!Int.!Int})
  a{b,e} b[:c,d:] send e 1 send c 2 send e 3 send d 4 send e 5
par_ten1_ten1 = proc(c : {[?Int], [!Int]})
  c{e,d} d[l] e[h]
  recv h (x : Int) send l x
-- Accepted by the checker, makes the compiler loop
par_ten_ten_v0 = proc(c : {[?Int, !Int], [!Int, ?Int]})
  c{e,d} d[k,l] e[h,g]
  ( ( recv h (x : Int)
    | ( send k 1 | recv l (y : Int) )
    )
  | send g 2
  )
par_ten_ten_v1 = proc(c : {[?Int, !Int], [!Int, ?Int]})
  c{e,d} d[k,l] e[h,g]
  ( recv h (x : Int)
  | send k 1
  | recv l (y : Int)
  | send g 2
  )
par_ten_ten_v2 = proc(c : {[?Int, !Int], [!Int, ?Int]})
  c{e,d} d[k,l] e[h,g]
  ( ( send k 1
    | ( recv h (x : Int) | recv l (y : Int) )
    )
  | send g 2
  )
pattern_example_expanded =
  proc(abcde : [!Int, [: !Int, !Int :], { [!Int, !Int], {?Int, ?Int} } ])
    abcde[a, bc, de]
    bc[: b, c :]
    de{d, e}
    (send a 1 | send b 2. send c 3 | fwd [!Int,!Int] (d,e))
plug_compose =
  \(A B C : Session)
   (p : < A, B >)
   (q : < ~B, C >)->
  proc(a : A, c : C)
    new [b : B, b' : ~B].
    ( @p(a, b)
    | @q(b', c))
-- plug_compose_par_par is a variation over plug_compose which is derived from
-- plug_compose. This shows how one can convert between <A,B> and <{A,B}>.

flat_par' =
  \(A B : Session)
   (p : < {A, B} >)->
  proc(a : A, b : B)
    new [ab : {A, B}, nanb].
    ( @p(ab)
    | nanb[na,nb]
      ( fwd(A)(a,na)
      | fwd(B)(b,nb)))

bump_par' =
  \(A B : Session)
   (p : < A, B >)->
  proc(ab : {A, B})
    ab{a,b}
    @p(a,b)

plug_compose' =
  \(A B C : Session)
   (p : < A, B >)
   (q : < ~B, C >)->
  proc(a : A, c : C)
    new [b : B, b' : ~B].
    ( @p(a, b)
    | @q(b', c))

plug_compose_par_par :
   (A B C : Session)
   (p : < { A, B} >)
   (q : < {~B, C} >)->
        < { A, C} >
  =
  \(A B C : Session)
   (p : < { A, B} >)
   (q : < {~B, C} >)->
   bump_par' A C (plug_compose' A B C (flat_par' A B p) (flat_par' (~B) C q))
plug_send_recv =
  \(p : < !Int, ?Int >)->
  proc(c : !Int, d : ?Int)
    @p(c,d)
_ = 1
_ = 2
_ = "Hello!"
test_receiver =
  \(A : Type)
   (S : A -> Session)
   (p : (x : A)-> < S x >)->
  proc(c)
    let x : A <- c.
    @(p x)(c)
assert 16 % 33 =  16
assert 30 + 2  =  32
assert 86 - 22 =  64
assert 4  * 32 = 128
assert 512 / 2 = 256
assert pow 2 9 = 512

assert (16 % 3)  ==I 16  = `false
assert (pow 2 9) ==I 512 = `true

assert 3.03 +D 0.11000000000000032 = 3.14
assert 3.28 -D 0.13999999999999968 = 3.14
assert 6.28 *D 0.5  = 3.14
assert 1.57 /D 0.5  = 3.14
assert powD 0.1 0.001 = 0.9977000638225533
assert 300000.0 *D 0.00001 = 3.0000000000000004

assert (300000.0 *D 0.00001) ==D 3.0000000000000004 = `true
assert (300000.0 *D 0.00001) ==D 3.0 = `false

assert Int2Double 42 = 42.0
assert (Int2Double 44) ==D 42.0 = `false
assert showInt 42 = "42"
assert (showInt 42) ==S "41" = `false
assert showDouble 3.14 = "3.14"
assert (showDouble 3.14) ==S "314" = `false
assert showChar 'a' = "'a'"
assert (showChar 'a') ==S "'a'" = `true
assert showString "Hello \"World\"!" = "\"Hello \\\"World\\\"!\""
assert (showString "Hello \"World\"!") ==S "" = `false
assert "Hello " ++S "World!" = "Hello World!"
assert let hello = "Hello " in
       let world = "Let!" in
       hello ++S world = "Hello Let!"
replicate =
  \ (A : Type)(n : Int)(x : A)->
  proc(os : [!A ^ n])
    split os as [o^n]
    parallel ^ n (o <- x)
-- should be named enum_par
replicate_par = proc(c : {!Int ^ 10})
  split c as {d^10}.
  sequence ^ 10 with i
    d <- i
replicate_proc =
  \ (A : Type)(n : Int)->
  proc(c : !A -o [!A ^ n])
    split c as {i,os}.
    let x : A <- i.
    split os as [o^n].
    parallel ^ n (o <- x)

replicate_proc_Int_10 = replicate_proc Int 10
tabulate_ten =
  \ (A : Type)(f : (i : Int)-> A)(n : Int)->
  proc(c : [ !A ^ n ])
    split c as [ c_ ^ n ]
    parallel ^ n with i (c_ <- (f i))

replicate_ten_10 = tabulate_ten Int (id Int) 10
rotate_seq = \ (A : Type)(n : Int)->
   proc(i : [: ?A ^(1 + n) :], o : [: !A ^(n + 1) :])
    split i as [:iL, iH^n:]
    split o as [:oL^n, oH:]
    let xL : A <- iL.
    -- TODO: fwd(?A ^ n)(iH, oL).
    sequence ^ n (fwd(?A)(iH, oL)).
    oH <- xL
test_sender =
  \(A : Type)
   (S : A -> Session)
   (t : A)
   (p : < S t >)->
    proc(c)
      c : !(x : A). S x <- t.
      @p(c)
seq0_explicit =
  proc(c : [: :])
  c[: :]
seq0 =
  proc(c : [: :])
  ()
seq3 = proc(c : [: !Int, !Int, !Int :])
  c[: c0, c1, c2 :]
  send c0 0
  send c1 1
  send c2 2

seq3_seq2 = proc(c : [: !Int, !Int, !Int :], d : [: !Int, !Int :])
  c[: c0, c1, c2 :]
  d[: d0, d1 :]
  send c0 0
  send c1 1
  send d0 0
  send c2 2
  send d1 1

seq_assoc_core =
 \(A B C : Session)->
 proc(i : ~[:[:A,B:],C:], o : [:A,[:B,C:]:])
  i[:nab,nc:]
  nab[:na,nb:]
  o[:a,bc:]
  bc[:b,c:]
  fwd(A)(a,na). fwd(B)(b,nb). fwd(C)(c,nc)
seq_par_back = proc(a : [:{!Int,!Int},!Int:])
  a[:b,e:] b{c,d} send c 2 send d 3 send e 1
seq_par_back_v2 = proc(a : [:{!Int,!Int},!Int:])
  a[:b,e:] b{c,d} send d 3 send c 2 send e 1
seq_pat = proc(c : [:?Int,!Int:])
  c[:d,e:]
  @(proc (f) f[:g,h:] fwd (?Int)(g,h))[:d,e:]
seq_seq = proc(a : [:[:!Int,!Int:],!Int:])
  a[:b,e:] b[:c,d:] send c 1 send d 2 send e 3
seq_seq_send2 = proc(a : [:[:!Int.!Int,!Int.!Int:],!Int.!Int:])
  a[:b,e:] b[:c,d:] send c 1 send c 2 send d 3 send d 4 send e 5 send e 6
seq_ten = proc(a : [:[!Int,!Int],!Int:])
  a[:b,e:] b[c,d] (send c 2 send e 1 | send d 3)
singleRecv = proc(c : ?Int) recv c (x : Int)
singleSend = proc(c : !Int) send c 42
sorter =
 \(n : Int)->
 proc(c : {? Vec Int n, ! Vec Int n})
  c{ci,co}
  recv ci (v : Vec Int n)
  send co (sort n v)
split_fwd1_rcv = proc(c : Fwd 1 (?Int)) c{d} fwd (?Int) (d)
split_nested_seq :
  (A B C D : Session)->
  < [: A, B, C, D :] -o [: [: A, B :], [: C, D :] :] > =
  \(A B C D : Session)->
   proc(c : {[: ~A, ~B, ~C, ~D :], [: [: A, B :], [: C, D :] :]})
    c{i,o}
    i[:na,nb,nc,nd:]
    o[:ab,cd:]
    ab[:a,b:]
    cd[:c,d:]
    fwd A (a,na).
    fwd B (b,nb).
    fwd C (c,nc).
    fwd D (d,nd)
sqr_dbl = proc(i: ?Int, o: !Int)
  let x : Int <- i.
  new/alloc (c :* Int).
  c <- (x * x).
  let y : Int <- c.
  o <- (y + y)

sqrs_body_session = !Int. ?Int. !Int. ?Int. !Int. ?Int

sqrs_body = \(x: Int)-> proc(c: sqrs_body_session, o: !Int)
  c <- (x * x).
  let x2: Int <- c.
  c <- (x2 * x2).
  let x4: Int <- c.
  c <- (x4 * x4).
  let x8: Int <- c.
  o <- (x8 * x8)

sqrs_main = proc(i: ?Int, o: !Int)
  let x: Int <- i.
  new/alloc (c :* Int).
  @(sqrs_body x)(c,o)
sqrs = proc(i: ?Int, o: !Int)
  let x : Int <- i.
  new/alloc (c :* Int).
  c <- (x * x).
  let x2 : Int <- c.
  c <- (x2 * x2).
  let x4 : Int <- c.
  c <- (x4 * x4).
  let x8 : Int <- c.
  o <- (x8 * x8)

sum_int = proc(a : {?Int ^ 10}, r : !Int)
  new/alloc (acc :* Int).
  acc <- 0.
  split acc as [: acci ^ 10, accn :].
  split a   as {  ai   ^ 10 }.
  sequence ^ 10 with i (
    let x : Int <- ai.
    let y : Int <- acci.
    acci <- (x + y)
  ).
  fwd(?Int)(accn, r)

switch
  : (A B C : Session)->
    < [A, {B, C}] -o {[A, B], C} >
  = \(A B C : Session)->
    -- The definition of `-o` is expanded to make it easier to follow the splits.
    proc(c : {{~A, [~B, ~C]}, {[A, B], C}})
      c{i,o}
      i{na,nbc}
      nbc[nb,nc]
      o{ab,c}
      ab[a,b]
      ( fwd A (a,na)
      | fwd B (b,nb)
      | fwd C (c,nc))
tabulate_seq =
  \ (A : Type)
    (f : (i : Int)-> A)
    (n : Int)->
  proc(a : [: !A^n :])
    split a as [: a_i^n :].
    sequence ^ n with i (a_i <- (f i))

tabulate_seq_Double_40 =
  tabulate_seq Double (\(i : Int)-> 1.0 -D (0.05 *D Int2Double i)) 41
ten_loli_par =
 \(A B : Session)->
 proc(c : [A,B] -o {A,B})
  c{i,o}
  i{na,nb}
  o{a,b}
  ( fwd(A)(a,na)
  | fwd(B)(b,nb))

ten_loli_par_sInt_sDouble = ten_loli_par (!Int) (!Double)
ten_loli_par_sequential =
 \(A B : Session)->
 proc(c : [A,B] -o {A,B})
  c{i,o}
  i{na,nb}
  o{a,b}
  fwd(A)(a,na).
  fwd(B)(b,nb)
ten_par_par_split = proc(c : [{},{}]) c[d,e] (d{} | e{})
tensor0 = proc(c : []) c[]
tensor1 = proc(c : [!Int]) c[d] send d 42
tensor2 = proc(c : [!Int,?Int]) c[d,e](recv e (x : Int) | send d 42)
tensor2_tensor0_tensor0_parallel = proc(cd : [[], []])
  cd[c,d] ( c[] | d[] )
{-
          d[] : [d : []]
       c[]d[] : [c : [], d : []]
cd[c,d]c[]d[] : [cd : [[], []]]
-}
tensor2_tensor0_tensor0_sequence = proc(cd : [[], []])
  cd[c,d] c[] d[]
tensor2_using_dual = proc(c : [!Int,~!Int]) c[d,e](recv e (x : Int) | send d 42)
test2 = proc()
  new [c : {?Int. !Int. ?Int, !Int. ?Int. !Int}, d].
  (
    c{c0,c1}
    recv c0 (x0 : Int)
    send c1 (x0 + 1)
    recv c1 (x1 : Int)
    send c0 (x1 + x0 + 2)
    recv c0 (x2 : Int)
    send c1 (x2 + x1 + x0 + 3)
  | d[d0,d1]
    (
      send d0 1
      recv d0 (y0 : Int)
      send d0 (y0 + 4)
    |
      recv d1 (z0 : Int)
      send d1 (z0 + 5)
      recv d1 (z1 : Int)
    )
  )
test3 = proc()
  new [c : ?Int. [!Int, !Int], d].
  (
    recv c (x0 : Int)
    c[c0,c1]
    ( send c0 x0 | send c1 x0 )
  |
    send d 1
    d{d0,d1}
    ( recv d0 (y0 : Int) | recv d1 (z0 : Int) )
  )
test4_inferred = proc(r)
  new [c, d].
  (
    recv c (x0 : Int)
    recv c (x1 : Int)
    recv c (x2 : Int)
    send r (x0 + x1 + x2)
  |
    send d 1
    send d 2
    send d 3
  )
test4 = proc(r : !Int)
  new [c : ?Int. ?Int. ?Int, d].
  (
    recv c (x0 : Int)
    recv c (x1 : Int)
    recv c (x2 : Int)
    send r (x0 + x1 + x2)
  |
    send d 1
    send d 2
    send d 3
  )
test_pat_term =
  proc(abcde : [!Int, [: !Int, !Int :], { [!Int, !Int], {?Int, ?Int} } ])
    abcde[a, bc, de]
    bc[: b, c :]
    de{d, e}
    (send a 1 | send b 2. send c 3 | fwd [!Int,!Int] (d,e))

-- notice how various parts gets commuted
test_pat =
  proc(bcaed : [[: !Int, !Int :], !Int, { {?Int, ?Int}, [!Int, !Int] } ])
    bcaed[bc, a, ed]
    bc[: b, c :]
    ed{e, d}
  @test_pat_term[a, [: b, c :], {d, e}]
type_annotation =
  ((21 + 21) : Int)
assert (`true : Bool) = `true : Bool
ZeroCh : Type
       = (A : Type)-> A

One : Type
    = (A : Type)(x : A)-> A

zeroOne : One
        = \(A : Type)(x : A)-> x

Two : Type
    = (A : Type)(x y : A)-> A

zeroTwo : Two
        = \(A : Type)(x y : A)-> x

oneTwo : Two
       = \(A : Type)(x y : A)-> y

notTwo : (b : Two)-> Two
       = \(b : Two)(A : Type)(x y : A)-> b A y x

notZero : Two =
  \(A : Type)(x y : A)->
    let A' = A in
    let x' = y in
    let y' = x in
    x'

notZero' : Two =
  let b = zeroTwo in
  \(A : Type)(x y : A)-> b A y x

notZero'' : Two = notTwo zeroTwo

assert notTwo zeroTwo = oneTwo : Two
assert notTwo oneTwo = zeroTwo : Two

andTwo : (b0 b1 : Two)-> Two
       = \(b0 b1 : Two)-> b0 Two zeroTwo b1

assert andTwo zeroTwo zeroTwo = zeroTwo : Two
assert andTwo zeroTwo oneTwo  = zeroTwo : Two
assert andTwo oneTwo  zeroTwo = zeroTwo : Two
assert andTwo oneTwo  oneTwo  = oneTwo  : Two

orTwo : (b0 b1 : Two)-> Two
      = \(b0 b1 : Two)-> b0 Two b1 oneTwo

assert orTwo zeroTwo zeroTwo = zeroTwo : Two
assert orTwo zeroTwo oneTwo  = oneTwo  : Two
assert orTwo oneTwo  zeroTwo = oneTwo  : Two
assert orTwo oneTwo  oneTwo  = oneTwo  : Two

Nat : Type
    = (A : Type)(z : A)(s : (n : A)-> A)-> A

zeroNat : Nat
        = \(A : Type)(z : A)(s : (n : A)-> A)-> z

sucNat : (n : Nat)-> Nat
       = \(n : Nat)(A : Type)(z : A)(s : (m : A)-> A)-> s (n A z s)

oneNat : Nat = sucNat zeroNat

twoNat : Nat = sucNat oneNat

threeNat : Nat = sucNat twoNat

fourNat : Nat = sucNat threeNat

fiveNat : Nat = sucNat fourNat

sixNat : Nat = sucNat fiveNat

addNat : (m n : Nat)-> Nat
       = \(m n : Nat)-> m Nat n sucNat

assert addNat zeroNat oneNat = oneNat : Nat
assert addNat oneNat zeroNat = oneNat : Nat

assert addNat twoNat threeNat = fiveNat : Nat

mulNat : (m n : Nat)-> Nat
       = \(m n : Nat)-> m Nat zeroNat (addNat n)

assert mulNat zeroNat oneNat  = zeroNat : Nat
assert mulNat oneNat  zeroNat = zeroNat : Nat
assert mulNat oneNat  oneNat  = oneNat  : Nat

assert mulNat oneNat oneNat
     = addNat oneNat zeroNat
     : Nat

assert mulNat twoNat threeNat
     = addNat threeNat (addNat threeNat zeroNat)
     : Nat

assert mulNat twoNat threeNat = sixNat : Nat

Bin : Type
    = (A : Type)(leaf : A)(fork : (left : A)(right : A)-> A)-> A

Nats : Type
     = (A : Type)(nil : A)(cons : (head : Nat)(tail : A)-> A)-> A

List : (X : Type)-> Type
     = \(X : Type)-> (A : Type)(nil : A)(cons : (head : X)(tail : A)-> A)-> A

nilList : (X : Type)-> List X
        = \(X : Type)(A : Type)(nil : A)(cons : (head : X)(tail : A)-> A)-> nil

consList : (X : Type)(head : X)(tail : List X)-> List X
         = \(X : Type)(head : X)(tail : List X)(A : Type)(nil : A)(cons : (head' : X)(tail' : A)-> A)->
           cons head (tail A nil cons)

mapList : (X Y : Type)(f : (x : X)-> Y)(xs : List X)-> List Y
        = \(X Y : Type)(f : (x : X)-> Y)(xs : List X)(A : Type)(nil : A)(cons : (head' : Y)(tail' : A)-> A)->
          xs A nil (\(head : X)(tail : A)-> cons (f head) tail)

-- -}
Id : (A : Type)(x y : A)-> Type

refl : (A : Type)(x : A)-> Id A x x

J : (A : Type)(x : A)(P : (y : A)(p : Id A x y)-> Type)(Px : P x (refl A x))(y : A)(p : Id A x y)-> P y p

J-refl : (A : Type)(x : A)(P : (y : A)(p : Id A x y)-> Type)(Px : P x (refl A x))->
         Id (P x (refl A x)) (J A x P Px x (refl A x)) Px

-- also called subst
tr : (A : Type)(x : A)(P : (y : A)-> Type)(Px : P x)(y : A)(p : Id A x y)-> P y
   = \(A : Type)(x : A)(P : (y : A)-> Type)(Px : P x)(y : A)(p : Id A x y)->
     J A x (\(z : A)(q : Id A x z)-> P z) Px y p

tr-refl : (A : Type)(x : A)(P : (y : A)-> Type)(Px : P x)->
          Id (P x) (tr A x P Px x (refl A x)) Px
        = \(A : Type)(x : A)(P : (y : A)-> Type)(Px : P x)->
          J-refl A x (\(z : A)(q : Id A x z)-> P z) Px

coe : (A B : Type)(p : Id Type A B)(x : A)-> B
    = \(A B : Type)(p : Id Type A B)(x : A)->
      tr Type A (\(X : Type)-> X) x B p

coe-refl : (A : Type)(x : A)-> Id A (coe A A (refl Type A) x) x
         = \(A : Type)(x : A)->
           tr-refl Type A (\(X : Type)-> X) x

sym : (A : Type)(x y : A)(p : Id A x y)-> Id A y x
    = \(A : Type)(x y : A)(p : Id A x y)-> tr A x (\(z : A)-> Id A z x) (refl A x) y p

trans : (A : Type)(x y z : A)(p : Id A x y)(q : Id A y z)-> Id A x z
     = \(A : Type)(x y z : A)(p : Id A x y)(q : Id A y z)->
        tr A y (Id A x) p z q
-- -}
uncurry =
  \(S T U : Session)->
  proc(c : (S -o T -o U) -o [S, T] -o U)
-- later on we could replace the 5 lines below by: c{[fx,[fy,fo]],{{x,y},o}}
  c{f,xyo}
  xyo{xy,o}
  xy{x,y}
  f[fx,fyo]
  fyo[fy,fo]
  ( fwd(S)(fx,x)
  | fwd(T)(fy,y)
  | fwd(U)(o,fo))
test_With  = \(SL SR : Session)-> ?(b : LR). (case b of { `left -> SL, `right -> SR })
test_with =
  \(SL SR : Session)
   (pL : < SL >)(pR : < SR >)->
  proc(c : test_With SL SR)
    let x : LR <- c.
    @(case x of { `left -> pL, `right -> pR })(c)
zap =
  \(S T : Session)(n : Int)->
  proc(c : [S -o T ^ n] -o [S ^ n] -o [T ^ n])
  split c   as {fs,xos}.
  split xos as {xs,os}.
  split fs  as {f^n}.
  split xs  as {x^n}.
  split os  as [o^n].
  parallel ^ n (
    split f as [fi,fo].
    ( fwd(S)(fi,x)
    | fwd(T)(o,fo)))

{- later on...
zap :  (S T : Session)(n : Int)-> < [S -o T ^ n] -o [S ^ n] -o [T ^ n] >
    = \(S T : Session)(n : Int)->
  proc{{f^n},{{x^n},[o^n]}}
  parallel ^ n
    fwd(S -o T){f, {x,o}}
-}
-- cf: would be more precise with {~(!Int -o !Int) ^ 10}
zap_ten_fwd = proc(cf : {?Int -o ?Int ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10])
  split cf as {cfi^10}.
  split cn as {cni^10}.
  split co as [coi^10].
  parallel ^ 10 (
    split cfi as {cfii,cfio}.
    ( fwd(?Int)(cni,cfii)
    | fwd(?Int)(cfio,coi)))
-- cf: would be more precise with {~(!Int -o !Int) ^ 10}
zap_ten_par = proc(cf : {(?Int -o ?Int) ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10])
  split cf as {cfi^10}.
  split cn as {cni^10}.
  split co as [coi^10].
  parallel ^ 10 (
    split cfi as {cfii,cfio}.
    ( let x : Int <- cni.
      cfii <- x
    | let y : Int <- cfio.
      coi <- y))
-- cf: would be more precise with {~(!Int -o !Int) ^ 10}
zap_ten_seq = proc(cf : {?Int -o ?Int ^ 10}, cn : {?Int ^ 10}, co : [!Int ^ 10])
  split cf as {cfi^10}.
  split cn as {cni^10}.
  split co as [coi^10].
  sequence ^ 10 (
    split cfi as {cfii,cfio}.
    let x : Int <- cni.
    cfii <- x.
    let y : Int <- cfio.
    coi <- y)
zip_add = proc(xs : {?Int ^ 10}, ys : {?Int ^ 10}, zs : [!Int ^ 10])
  split xs as {x^10}.
  split ys as {y^10}.
  split zs as [z^10].
  parallel ^ 10 (
    let a : Int <- x.
    let b : Int <- y.
    z <- (a + b))

-- This version is not as useful as fft_ten.ll or fft_seq.ll.
-- Indeed here we end up using `sync` instead of `schedule` which
-- compromises fusion.

{-
H : (A : Type)-> A

compH :
   (S T U : Session)
   (p : < S -o T >)-> < S -o U >

compHH :
   (S T U : Session)-> < S -o U >
-}

C = ComplexDouble
I = ComplexI

CT = [!C,!C]
CP = {!C,!C}

bff = \(tw : C)(i : Int)-> proc(xy : CP -o CT)
  split xy as {x,y}.
  split x  as [cx0, cx1].
  split y  as [y0, y1].
  ( let x0 : C <- cx0
  | let x1 : C <- cx1).
  let wkn = (x1 *CD cexp (tw *CD Int2ComplexDouble i)).
  ( y0 <- (x0 +CD wkn)
  | y1 <- (x0 -CD wkn))

mapi : (S T : Session)(p : (i : Int)-> < S -o T >)(n : Int)-> < { S ^ n } -o { T ^ n } >
   = \ (S T : Session)(p : (i : Int)-> < S -o T >)(n : Int)->
  proc(xys : { S ^ n } -o { T ^ n })
    split xys as {xs, ys}.
    split xs  as [x ^ n].
    split ys  as {y ^ n}.
    parallel ^ n with i (@(p i)(x,y))

map : (S T : Session)(p : < S -o T >)(n : Int)-> < { S ^ n } -o { T ^ n } >
  = \ (S T : Session)(p : < S -o T >)-> mapi S T (\(i : Int)-> p)

sync =
  \ (S : Session)(n : Int)->
  proc(xys : { Send S ^ n } -o [ Send S ^ n ])
    split xys as {xs, ys}.
    new/alloc [: ws : { Send S ^ n } , rs : { ~Send S ^ n } :].
    fwd({ Send S ^ n })(ws, xs).
    fwd([ Send S ^ n ])(ys, rs)

twist =
  \ (S T : Session)
    (p : < ~T -o ~S >)->
  proc(st : S -o T)
    split st as {s,t}.
    @p{t,s}

comp =
  \ (S T U : Session)
    (p : < S -o T >)
    (q : < T -o U >)->
  proc(su : S -o U)
    split su as {sn,u}.
    new [ t : T, tn : ~T ].
    ( @p{sn, t} | @q{tn, u})

pmoc =
  \ (S T U : Session)
    (p : < ~T -o ~S >)
    (q : < T -o U >)-> comp S T U (twist S T p) q

-- their sig:   Ten^2n(C) -> Ten^n(C) ⊗ Ten^n(C)
-- they derive: Ten^2n(C), Par^n(~C) ⅋ Par^n(~C) ⊢
-- our sig:     { S ^(n + n) } -o { { S ^ n }, { S ^ n } }
-- we derive: ⊢ [ ~S ^(n + n) ], { { S ^ n }, { S ^ n } }
-- Given `C = ~ S` we can say we both derive the same sequent.
-- However 
halve =
  \ (S : Session)(n : Int)->
  proc(xys : { S ^(n + n) } -o { { S ^ n }, { S ^ n } })
    split xys as {xs, ys}.
    split xs  as [xL ^ n, xH ^ n].
    split ys  as {ysL, ysH}.
    split ysL as {yL ^ n}.
    split ysH as {yH ^ n}.
    ( parallel ^ n (fwd(S)(yL, xL))
    | parallel ^ n (fwd(S)(yH, xH)))

zip =
  \ (S T : Session)(n : Int)->
  proc(xyzs : { { S ^ n }, { T ^ n } } -o { {S, T} ^ n })
    split xyzs as {xys, zs}.
    split xys  as [xs, ys].
    split xs   as [x ^ n].
    split ys   as [y ^ n].
    split zs   as {z ^ n}.
    parallel ^ n (
      split z as {z0, z1}.
      ( fwd(S)(z0,x)
      | fwd(T)(z1,y)))

fft_comp :   (n : Int)-> < { !C ^(n + n) } -o [ !C ^(n + n) ] >
         = \ (n : Int)->
  let tw = (I *CD Double2Complex (2.0 *D (PI /D Int2Double n))) in
        (halve (!C) n)
  =/|/= (zip (!C) (!C) n)
  =/|/= (mapi CP CT (bff tw) n)
  =/|/= (sync CT n)
  =/|/= (zip (?C) (?C) n)
  /=|=/ (halve (?C) n)

fft :   (n : Int)-> < { !C ^(n + n) } -o [ !C ^(n + n) ] >
    = \ (n : Int)->
  let tw = (I *CD Double2Complex (2.0 *D (PI /D Int2Double n))) in
  let CnP = { !C ^ n } in
  let CnT = [ !C ^ n ] in
  let CnTT = [CnT, CnT] in
  let CnPP = {CnP, CnP} in
  let CPnP = { {!C, !C} ^ n } in
  let CTnP = { [!C, !C] ^ n } in
  let CTnT = [ [!C, !C] ^ n ] in
  let C2nT = [ !C ^(n + n) ] in
  let C2nP = { !C ^(n + n) } in
  comp C2nP CnPP C2nT (halve (!C) n) (
  comp CnPP CPnP C2nT (zip (!C) (!C) n) (
  comp CPnP CTnP C2nT (mapi CP CT (bff tw) n) (
  comp CTnP CTnT C2nT (sync CT n) (
  pmoc CTnT CnTT C2nT (zip (?C) (?C) n) (
  twist     CnTT C2nT (halve (?C) n))
  ))))

fft_10 = fft 10

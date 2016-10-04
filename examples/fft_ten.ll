{-
H : (A : Type)-> A

compH :
   (S T U : Session)
   (p : < S -o T >)-> < S -o U >

compHH :
   (S T U : Session)-> < S -o U >
-}

C : Type
addC : C -> C -> C
subC : C -> C -> C
mulC : C -> C -> C
wkn : C

CT = [!C,!C]
CP = {!C,!C}

bff = proc(xy : CT -o CP)
  split xy as {x,y}.
  split x  as {cx0, cx1}.
  split y  as {y0, y1}.
  ( let x0 : C <- cx0
  | let x1 : C <- cx1).
  ( y0 <- (addC x0 (mulC x1 wkn))
  | y1 <- (subC x0 (mulC x1 wkn)))
{- Alternatively
  let x0 : C <- cx0.
  let x1 : C <- cx1.
  y0 <- (addC x0 (mulC x1 wkn)).
  y1 <- (subC x0 (mulC x1 wkn))
-}

map : (S T : Session)(p : < S -o T >)(n : Int)-> < [ S ^ n ] -o [ T ^ n ] >
  = \ (S T : Session)(p : < S -o T >)(n : Int)->
  proc(xys : [ S ^ n ] -o [ T ^ n ])
    split xys as {xs, ys}.
    split xs  as {x ^ n}.
    split ys  as [y ^ n].
--proc{ [ x ^ n ], [ y ^ n ] }
    parallel ^ n (@p(x,y))

schedule =
  \ (S : Session)(n : Int)->
  proc(xys : [ S ^ n ] -o { S ^ n })
    split xys as {xs, ys}.
    split xs  as {x ^ n}.
    split ys  as {y ^ n}.
    parallel ^ n (fwd(S)(y,x))

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

funProc : (A B : Type)(f : A -> B)-> < !A -o !B >
      = \ (A B : Type)(f : A -> B)->
  proc(a : ?A, b : !B)
    let av : A <- a.
    b <- (f av)

length : String -> Int

test_map_map =
  comp [ !Int ^ 10 ] [ !String ^ 10 ] [ !Int ^ 10 ]
       (map (!Int) (!String) (funProc Int String showInt) 10)
       (map (!String) (!Int) (funProc String Int length)  10)

{-
test_map_map_alloc =
  proc (su : {{?Int ^ 10},[!Int ^ 10]})
  split su {sn, u}.
  new [t : [!String ^ 10],tn : {?String ^ 10}].
  ( split sn {x ^ 10}.
    split t [y ^ 10].
    parallel ^ 10 (
      let av : Int <- x.
      y <- (showInt av))
  | split tn {xq ^ 10}.
    split u [yq ^ 10].
    parallel ^ 10 (
      let avq : String <- xq.
      yq <- (length avq)))

test_map_map_fuse1 =
  proc (su : {{?Int ^ 10},[!Int ^ 10]})
  split su {sn, u}.
  split sn {x ^ 10}.
  split u [yq ^ 10].
  parallel ^ 10 (
    new [y : !String,xq : ?String].
    ( let av : Int <- x.
      y <- (showInt av)
    | let avq : String <- xq.
      yq <- (length avq)) )

test_map_map_fuse2 =
  proc (su : {{?Int ^ 10},[!Int ^ 10]})
  split su {sn, u}.
  split sn {x ^ 10}.
  split u [yq ^ 10].
  parallel ^ 10 (
    let av : Int <- x.
    let avq : String = (showInt av).
    yq <- (length avq))
-}

-- their sig:   Ten^2n(S) -> Ten^n(S) ⊗ Ten^n(S)
-- they derive: Ten^2n(S), Par^n(~S) ⅋ Par^n(~S) ⊢
-- our sig:     [ S ^(n + n) ] -o [ [ S ^ n ], [ S ^ n ] ]
-- we derive: ⊢ { ~S ^(n + n) }, [ [ S ^ n ], [ S ^ n ] ]
-- By moving formulas across `⊢` we can conclude that we
-- both derive the same sequent.
-- However their elimination of tensor on left corresponds
-- to the introduction of a par on the right and their elimination
-- of a par on the left corresponds to the introduction of a tensor
-- on the right.
{-
halve : (S : Session)(n : Int)-> < [ S ^(n + n) ] -o [ [ S ^ n ], [ S ^ n ] ] >
    = \ (S : Session)(n : Int)->
  proc(xys : [ S ^(n + n) ] -o [ [ S ^ n ], [ S ^ n ] ])
    split xys as {xs, ys}.
    split xs  as {xL ^ n, xH ^ n}.
    split ys  as [ysL, ysH].
    split ysL as [yL ^ n].
    split ysH as [yH ^ n].
--proc{{ xL ^ n, xH ^ n }, [ [ yL ^ n ], [ yH ^ n ] ]}
    ( parallel ^ n (fwd(S)(yL, xL))
    | parallel ^ n (fwd(S)(yH, xH)))

zip : (S T : Session)(n : Int)-> < [ [ S ^ n ], [ T ^ n ] ] -o [ [ S, T ] ^ n ] >
  = \ (S T : Session)(n : Int)->
  proc(xyzs : [ [ S ^ n ], [ T ^ n ] ] -o [ [ S, T ] ^ n ])
    split xyzs as {xys, zs}.
    split xys  as {xs, ys}.
    split xs   as {x ^ n}.
    split ys   as {y ^ n}.
    split zs   as [z ^ n].
--proc{ { { x ^ n }, { y ^ n } }, [ z ^ n ] }
    parallel ^ n (
      split z as [z0, z1].
      ( fwd(S)(z0,x)
      | fwd(T)(z1,y)))

fft_comp : (n : Int)-> < [!C ^(n + n)] -o {!C ^(n + n)} >
  = \(n : Int)->
        (halve (!C) n)
  =/|/= (zip (!C) (!C) n)
  =/|/= (map CT CP bff n)
  =/|/= (schedule CP n)
  =/|/= (zip (?C) (?C) n)
  /=|=/ (halve (?C) n)

fft :   (n : Int)-> < [!C ^(n + n)] -o {!C ^(n + n)} >
    = \ (n : Int)->
  let Cn = [ !C ^ n ] in
  let CnPP = {{!C ^ n}, {!C ^ n}} in
  let CnT = [Cn, Cn] in
  let CPnP = { {!C, !C} ^ n } in
  let CPnT = [ {!C, !C} ^ n ] in
  let CTnT = [ [!C, !C] ^ n ] in
  let C2nT = [ !C ^(n + n) ] in
  let C2nP = { !C ^(n + n) } in
  comp C2nT CnT  C2nP (halve (!C) n) (
  comp CnT  CTnT C2nP (zip (!C) (!C) n) (
  comp CTnT CPnT C2nP (map CT CP bff n) (
  comp CPnT CPnP C2nP (schedule {!C, !C} n) (
  pmoc CPnP CnPP C2nP (zip (?C) (?C) n) (
  twist     CnPP C2nP (halve (?C) n))
  ))))

fft_10 = fft 10
-- -}

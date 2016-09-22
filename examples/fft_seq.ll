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

bff = proc(xy : CP -o CT)
  split xy as {x,y}.
  split x  as [cx0, cx1].
  split y  as [y0, y1].
  ( let x0 : C <- cx0
  | let x1 : C <- cx1).
  ( y0 <- (addC x0 (mulC x1 wkn))
  | y1 <- (subC x0 (mulC x1 wkn)))

map =
  \ (S T : Session)(p : < S -o T >)(n : Int)->
  proc(xys : [: S ^ n :] -o [: T ^ n :])
    split xys as {xs, ys}.
    split xs  as [: x ^ n :].
    split ys  as [: y ^ n :].
    sequence ^ n (@p(x,y))

map_bff : (n : Int)-> < [: CP ^ n :] -o [: CT ^ n :] >
        = map CP CT bff

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

halve =
  \ (S : Session)(n : Int)->
  proc(xys : [: S ^(n + n) :] -o {[: S ^ n :], [: S ^ n :]})
    split xys as {xs, ys}.
    split xs  as [: xL ^ n, xH ^ n :].
    split ys  as { ysL, ysH }.
    split ysL as [: yL ^ n :].
    split ysH as [: yH ^ n :].
    sequence ^ n (fwd(S)(yL, xL)).
    sequence ^ n (fwd(S)(yH, xH))

zip =
  \ (S T : Session)(n : Int)->
  proc(xyzs : { [: S ^ n :], [: T ^ n :] } -o [: {S, T} ^ n :])
    split xyzs as {xys, zs}.
    split xys  as [xs, ys].
    split xs   as [: x ^ n :].
    split ys   as [: y ^ n :].
    split zs   as [: z ^ n :].
    sequence ^ n (
      split z as {z0, z1}.
      ( fwd(S)(z0,x)
      | fwd(T)(z1,y)))

fft =
  \ (n : Int)->
    let Cn = [: !C ^ n :] in
    let CnP = {Cn, Cn} in
    let CnT = [Cn, Cn] in
    let CPn = [: {!C, !C} ^ n :] in
    let CTn = [: [!C, !C] ^ n :] in
    let C2n = [: !C ^(n + n) :] in
    comp C2n CnP C2n (halve (!C) n) (
    comp CnP CPn C2n (zip (!C) (!C) n) (
    comp CPn CTn C2n (map_bff n) (
    pmoc CTn CnT C2n (zip (?C) (?C) n) (
    twist CnT C2n    (halve (?C) n)))))

fft_10 = fft 10

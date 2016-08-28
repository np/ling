zipWith =
  \(A B C : Type)
   (f : (a : A)(b : B)-> C)
   (n : Int)->
  proc(cas : [: ?A ^ n :], cbs : [: ?B ^ n :], ccs : [: !C ^ n :])
    split cas[:ca^n:]
    split cbs[:cb^n:]
    split ccs[:cc^n:]
    slice (ca,cb,cc) n as _
      -- could be parallel
      let a : A <- ca.
      let b : B <- cb.
      cc <- (f a b)

{-
zipWith =
  \(A B C : Type)
   (f : (a : A)(b : B)-> C)
   (n : Int)->
  proc([: ca : ?A ^ n :], [: cb : ?B ^ n :], [: cc : !C ^ n :])
    slice (ca,cb,cc) n as _
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
  new/alloc [itmp : !B. ?B, tmp]
  ( itmp <- init.
    fwd(?B)(itmp, cr)
  | split ca[: ai^n :]
    slice (ai) n as _
      ( let a : A <- ai
      | let b : B <- tmp).
      tmp <- (f b a))

sumD : (n : Int)-> < [: ?Double ^ n :], !Double >
     = foldl Double Double _+D_ 0.0

dotproduct = \(n : Int)->
  proc(as' : [: ?Double ^ n :], bs : [: ?Double ^ n :], o : !Double)
    -- TODO fusion
    new/alloc [: cs : [: !Double ^ n :], ds :].
    @(zip_multD n){as', bs, cs}.
    @(sumD n){ds, o}

dotproduct_4 = dotproduct 4

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
  slice (v_i) n as j
    v_i <- (ix A (m * n) a ((i * n) + j))

col = \(A : Type)(m n : Int)(a : Vec A (m * n))(j : Int)-> proc(v : [: !A^m :])
  split v [: v_j^m :].
  slice (v_j) m as i
    v_j <- (ix A (m * n) a ((i * n) + j))

matmult = \(m n p : Int)->
           proc(a : ?Vec Double (m * n),
                b : ?Vec Double (n * p),
                c : [: !Double^(m * p) :])
  let a' : Vec Double (m * n) <- a.
  let b' : Vec Double (n * p) <- b.
  split c   [: c_i_j^(m * p) :].
  slice (c_i_j) (m * p) as ij
    new/alloc [: u : [: !Double^n :], u' :].
    @(row Double m n a' (ij / n))(u).
    new/alloc [: v : [: !Double^n :], v' :].
    @(col Double n p b' (ij % n))(v).
    -- Working around a bug name-binding bug...
    let nn = n.
    @(dotproduct nn){u',v',c_i_j}

matmult_4 = matmult 4 4 4

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

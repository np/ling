ZeroCh : Type
       = (A : Type)-> A

One : Type
    = (A : Type)(x : A)-> A

zeroOne : One
        = \(A : Type)(x : A)-> x

Two : Type
    = (A : Type)(x : A)(y : A)-> A

zeroTwo : Two
        = \(A : Type)(x : A)(y : A)-> x

oneTwo : Two
       = \(A : Type)(x : A)(y : A)-> y

notTwo : (b : Two)-> Two
       = \(b : Two)(A : Type)(x : A)(y : A)-> b A y x

andTwo : (b0 : Two)(b1 : Two)-> Two
       = \(b0 : Two)(b1 : Two)-> b0 Two zeroTwo b1

orTwo : (b0 : Two)(b1 : Two)-> Two
      = \(b0 : Two)(b1 : Two)-> b0 Two b1 oneTwo

Nat : Type
    = (A : Type)(z : A)(s : (n : A)-> A)-> A

zeroNat : Nat
        = \(A : Type)(z : A)(s : (n : A)-> A)-> z

sucNat : (n : Nat)-> Nat
       = \(n : Nat)(A : Type)(z : A)(s : (m : A)-> A)-> s (n A z s)

addNat : (m : Nat)(n : Nat)-> Nat
       = \(m : Nat)(n : Nat)-> m Nat n sucNat

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

mapList : (X : Type)(Y : Type)(f : (x : X)-> Y)(xs : List X)-> List Y
        = \(X : Type)(Y : Type)(f : (x : X)-> Y)(xs : List X)(A : Type)(nil : A)(cons : (head' : Y)(tail' : A)-> A)->
          xs A nil (\(head : X)(tail : A)-> cons (f head) tail)

-- -}

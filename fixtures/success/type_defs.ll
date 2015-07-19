Zero : Type
     = (A : Type)-> A
     .

One  : Type
     = (A : Type)(x : A)-> A
     .

Two  : Type
     = (A : Type)(x : A)(y : A)-> A
     .

Nat  : Type
     = (A : Type)(z : A)(s : (n : A)-> A)-> A
     .

Bin  : Type
     = (A : Type)(leaf : A)(fork : (left : A)(right : A)-> A)-> A
     .

Nats : Type
     = (A : Type)(nil : A)(cons : (head : Nat)(tail : A)-> A)-> A
     .

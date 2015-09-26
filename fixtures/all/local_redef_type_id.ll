Id : (A : Type)(x : A)(y : A)-> Type

refl : (A : Type)(x : A)-> Id A x x

J : (A : Type)(x : A)(P : (y : A)(p : Id A x y)-> Type)(Px : P x (refl A x))(y : A)(p : Id A x y)-> P y p

-- also called subst
tr : (A : Type)(x : A)(P : (y : A)-> Type)(Px : P x)(y : A)(p : Id A x y)-> P y
   = \(A : Type)(x : A)(P : (y : A)-> Type)(Px : P x)(y : A)(p : Id A x y)->
     J A x (\(y : A)(p : Id A x y)-> P y) Px y p

coe : (A : Type)(B : Type)(p : Id Type A B)(x : A)-> B
    = \(A : Type)(B : Type)(p : Id Type A B)(x : A)->
      tr Type A (\(X : Type)-> X) x B p

sym : (A : Type)(x : A)(y : A)(p : Id A x y)-> Id A y x
    = \(A : Type)(x : A)(y : A)(p : Id A x y)-> tr A x (\(y : A)-> Id A y x) (refl A x) y p

trans : (A : Type)(x' : A)(y' : A)(z' : A)(p : Id A x' y')(q : Id A y' z')-> Id A x' z'
      = \(A : Type)(x' : A)(y' : A)(z' : A)(p : Id A x' y')(q : Id A y' z')->
        tr A y' (Id A x') p z' q

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

Id : (A : Type)(x : A)(y : A)-> Type.

sym : (A : Type)(x : A)(y : A)(p : Id A x y)-> Id A y x
    = \(A : Type)(x : A)(y : A)(p : Id A x y)-> p.

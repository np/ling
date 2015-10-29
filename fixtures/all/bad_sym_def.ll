Id : (A : Type)(x y : A)-> Type

sym : (A : Type)(x y : A)(p : Id A x y)-> Id A y x
    = \(A : Type)(x y : A)(p : Id A x y)-> p

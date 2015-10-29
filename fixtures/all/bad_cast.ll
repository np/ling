Id : (A : Type)(x y : A)-> Type

refl : (A : Type)(x : A)-> Id A x x

bad : (A : Type)(x y : A)-> Id A x y
    = \(A : Type)(x y : A)-> refl A x

Id : (A : Type)(x : A)(y : A)-> Type.

refl : (A : Type)(x : A)-> Id A x x.

bad : (A : Type)(x : A)(y : A)-> Id A x y
    = \(A : Type)(x : A)(y : A)-> refl A x.

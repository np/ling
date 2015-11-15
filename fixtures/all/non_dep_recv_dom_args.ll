assert (A : Type)(a0 : A)(B : (a : A)-> Type)-> < ?     B a0  >
     = (A : Type)(a0 : A)(B : (a : A)-> Type)-> < ?(b : B a0) >
     : Type

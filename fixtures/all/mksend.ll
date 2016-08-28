mksend = \(A : Type)(x : A)-> proc(a : !A) a <- x

mksendInt42 = mksend Int 42

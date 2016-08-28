mkrecv = \(A : Type)-> proc(a : ?A) let x : A <- a

mkrecvInt = mkrecv Int

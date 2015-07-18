data T = `c | `d.
data U = `e | `f.

badTU : (t : T)-> U = \(t : T)-> case t of { `e -> `c, `f -> `d }.

-- At first we were rejecting it under the basis
-- that d{} should be in parallel with e{} since
-- d and e are in tensor. Since this is harmless
-- and avoids a special case in the checker we
-- now accept it.
ten_par_par_seq = proc(c : [{},{}]) c[d,e] d{} e{}

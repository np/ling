test_With  = \(SL SR : Session)-> ?(b : LR). (case b of { `left -> SL, `right -> SR })
test_with =
  \(SL SR : Session)
   (pL : < SL >)(pR : < SR >)->
  proc(c : test_With SL SR)
    let x : LR <- c.
    @(case x of { `left -> pL, `right -> pR })(c)

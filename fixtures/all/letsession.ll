letsession =
  let f = \(S0 : Session)->
            let S1 = {S0,S0} in
            let S2 = {S1,S1} in
            let S3 = {S2,S2} in
            let S4 = {S3,S3} in
            let S5 = {S4,S4} in
            let S6 = {S5,S5} in
            let S7 = {S6,S6} in
            S7
  in
  proc(c)
  fwd 2 (f (?Int)) c

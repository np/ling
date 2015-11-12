-- while wrong_case_con reduces to 1 which is well-typed a part of it is not
wrong_case_con = case `true of { `true -> 1, `false -> 1 + `true }

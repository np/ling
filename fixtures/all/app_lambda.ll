app_lambda = (\(x : Int)-> x + x) 21
app_lambda_2 = (\(x : Int)(y : Int)-> x + y) 21 42
app_lambda_let =
  (let x = 21 in \(y : Int)-> x + y) (let notx = 7 in notx + notx + notx)

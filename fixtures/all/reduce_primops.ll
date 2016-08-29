assert 16 % 33 =  16
assert 30 + 2  =  32
assert 86 - 22 =  64
assert 4  * 32 = 128
assert 512 / 2 = 256
assert pow 2 9 = 512

assert (16 % 3)  ==I 16  = `false
assert (pow 2 9) ==I 512 = `true

assert 3.03 +D 0.11000000000000032 = 3.14
assert 3.28 -D 0.13999999999999968 = 3.14
assert 6.28 *D 0.5  = 3.14
assert 1.57 /D 0.5  = 3.14
assert powD 0.1 0.001 = 0.9977000638225533
assert 300000.0 *D 0.00001 = 3.0000000000000004

assert (300000.0 *D 0.00001) ==D 3.0000000000000004 = `true
assert (300000.0 *D 0.00001) ==D 3.0 = `false

assert Int2Double 42 = 42.0
assert (Int2Double 44) ==D 42.0 = `false
assert showInt 42 = "42"
assert (showInt 42) ==S "41" = `false
assert showDouble 3.14 = "3.14"
assert (showDouble 3.14) ==S "314" = `false
assert showChar 'a' = "'a'"
assert (showChar 'a') ==S "'a'" = `true
assert showString "Hello \"World\"!" = "\"Hello \\\"World\\\"!\""
assert (showString "Hello \"World\"!") ==S "" = `false
assert "Hello " ++S "World!" = "Hello World!"
assert let hello = "Hello " in
       let world = "Let!" in
       hello ++S world = "Hello Let!"

assert 16 % 33 =  16
assert 30 + 2  =  32
assert 86 - 22 =  64
assert 4  * 32 = 128
assert 512 / 2 = 256
assert pow 2 9 = 512

assert 3.03 +D 0.11000000000000032 = 3.14
assert 3.28 -D 0.13999999999999968 = 3.14
assert 6.28 *D 0.5  = 3.14
assert 1.57 /D 0.5  = 3.14
assert powD 0.1 0.001 = 0.9977000638225533

assert Int2Double 42 = 42.0
assert showInt 42 = "42"
assert showDouble 3.14 = "3.14"
assert showChar 'a' = "'a'"
assert showString "Hello \"World\"!" = "\"Hello \\\"World\\\"!\""
assert "Hello " ++S "World!" = "Hello World!"
assert let hello = "Hello " in
       let world = "Let!" in
       hello ++S world = "Hello Let!"

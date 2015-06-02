This is a tutorial for Lin language. Concepts, constructs and idoms are
introduced through a series of examples.

# Send and receive, atomic sessions

## A first example

We start with a "doubling server" which receives one integer `n` on the channel
`rn` (`r` stands for `receive`), and *then* sends `n+n` on the channel `sdbl`
(`s` stands for `send`).

```
double_server(rn : ?Int, sdbl : !Int) =
  recv rn   (n : Int)
  send sdbl (n + n)
.
```

The *session* type for the channels indicates the protocol to follow on such
channel. For any type `A` (such as `Int`), the session `?A`, means to receive
an `A` and the `!A` means to send an `A`.

The *process* is then made of two commands here. The command `recv c (x : A)`
receives on the channel `c` and then _binds_ the received _term_ to the
_variable_ `x`. The command `send c t` sends on the channel `c` the term `t`.

When running processes in a closed _term context_ the terms being communicated
can first be evaluated as _values_.

The types of _definitions_ such as `+` and types `Int` are given as a
_signature_. For now let's assume the following signature:

~~~
Int : Type.
_+_ : (m : Int)(n : Int) -> Int.
_/_ : (m : Int)(n : Int) -> Int.
_%_ : (m : Int)(n : Int) -> Int.
~~~

## Channel allocation and parallel composition

How to use our doubling server. The following process has one given channel
`sdbl` on which it should send an `Int`. To do so one first allocate a new
channel which introduces two endpoints: `rn` and `sn`. Then one describe
two processes which are composed in parallel `(P | Q)`. On the left a reference
to our doubling server which should receive on `rn` and send on `sdbl`. On
the right the process sends the value `21` on the channel `sn`. Since `rn` and
`sn` are the two endpoint of the same channel, sending `21` on `sn` is received
on `rn`, then bound as `n`, then the send command is ready to send `21 + 21`
hence `42`.

~~~
double_21(sdbl : !Int) =
  new (rn : ?Int, sn : !Int)
  (
    @double_server(rn, sdbl)
  |
    send sn 21
  )
.
~~~

The reference to a previous defined process is equivalent to substituting the
definition in place of the reference, potentially renaming the channel names
to match the ones in the reference. Here is the previous example, expanded:

```
double_21_expanded (sdbl : !Int) =
  new (rn : ?Int, sn : !Int)
  (
    recv rn   (n : Int)
    send sdbl (n + n)
  |
    send sn 21
  )
.
```

The semantics of `double_21(s)` is equivalent to `send s 42`.

More generally the process
`new (r : ?A, s : !A) (recv r (n : A) P | send s t Q)`
is equivalent to the process
`(P[n := t] | Q)` where one substituted `t` for `n` in `P`.

The parallel composition of processes is commutative and associative which
is a quite important property.

More formally for all processes `P`, `Q`, and `R`,
`(P|Q)` is equivalent to `(Q|P)` and `(P|(Q|R))` is equivalent to `((P|Q)|R)`.

One can thus compose processes with no particular nesting: `(P|Q|R|S)`.

## Sending two results

Our next example is a simple server to compute division and modulus of two `Int`.
In contrast to functional programming there is no need to package the two result
as a single one using a tuple. Actually this might look like an imperative
program where two addresses are given to write the two results instead of
"returning" them. These processes are actually a lot more functional that they
look like and enjoy similar properties.

```
div_mod_server (rm : ?Int, rn : ?Int, sdiv : !Int, smod : !Int) =
  recv rm (m : Int)
  recv rn (n : Int)
  send sdiv (m / n)
  send smod (m % n)
.
```

Exchanging the order of the two `recv` commands yields to an equivalent process.
Similarily with exchanging the `send` commands. One can even compose them in
parallel:

```
div_mod_server_explicit_prll (rm : ?Int, rn : ?Int, sdiv : !Int, smod : !Int) =
  recv rn (n : Int)
  recv rm (m : Int)
  (send sdiv (m / n) | send smod (m % n))
.
```

## ...

```
div_mod_server_par4 (c : {?Int, ?Int, !Int, !Int}) =
  c{rm,rn,sdiv,smod}
  recv rm (m : Int)
  recv rn (n : Int)
  send sdiv (m / n)
  send smod (m % n)
.
```

same flexibility as in `div_mod_server`

```
div_mod_server_seq4 (c : [: ?Int, ?Int, !Int, !Int :]) =
  c{rm,rn,sdiv,smod}
  recv rm (m : Int)
  recv rn (n : Int)
  send sdiv (m / n)
  send smod (m % n)
.
```

no flexibility has to be this order.

```
div_mod_server_par3_ten2 (c : {?Int, ?Int, [!Int, !Int]}) =
  c{rm,rn,s}
  s[sdiv,smod]
  recv rm (m : Int)
  recv rn (n : Int)
  ( send sdiv (m / n)
  | send smod (m % n) )
.
```

`s[sdiv,smod]` and the `recv` can commute.

```
div_mod_server_cont (c : ?Int.?Int.!Int.!Int) =
  recv c (m : Int)
  recv c (n : Int)
  send c (m / n)
  send c (m % n)
.
```

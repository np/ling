% ling: Programing with linear types, a tutorial
% Nicolas Pouillard
% 2015-06-04, Agda Intensive Meeting XXI

and Daniel Gustafsson (ITU, IT University of Copenhagen)

This is a tutorial for Ling language. Concepts, constructs and idoms are
introduced through a series of examples.

# A glimpse of the goal

This process is reading an array

```
sum_int (a : {?Int ^ 10}, r : !Int) =
  new (itmp : !Int.?Int, tmp)
  ( send itmp 0
    fwd(?Int)(itmp, r)
  |
    a{ai}
    slice (ai) 10 as i
    recv ai  (x : Int)
    recv tmp (y : Int)
    send tmp (x + y)
  )
.
```

```{.c}
void sum_int(const int a[10], int *r) {
  int itmp;
  itmp = 0;
  for (int i = 0; i < 10; i = i + 1) {
    const int x = a[i];
    const int y = itmp;
    itmp = x + y;
  };
  const int z = itmp;
  *r = z;
}
```

# Send and receive: atomic sessions

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

## Sending two results (in parallel)

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

## Continued sessions: imposing a strict processing order

```
div_mod_server_cont (c : ?Int.?Int.!Int.!Int) =
  recv c (m : Int)
  recv c (n : Int)
  send c (m / n)
  send c (m % n)
.
```

## Sequences(`»`/`[::]`): Fixed, left-to-right processing order

```
div_mod_server_seq4 (c : [: ?Int, ?Int, !Int, !Int :]) =
  c[:rm,rn,sdiv,smod:]
  recv rm (m : Int)
  recv rn (n : Int)
  send sdiv (m / n)
  send smod (m % n)
.
```

No flexibility. It has to be in this order.

## Par(`⅋`/`{}`): You control the processing order!

```
div_mod_server_par4 (c : {?Int, ?Int, !Int, !Int}) =
  c{rm,rn,sdiv,smod}
  recv rm (m : Int)
  recv rn (n : Int)
  send sdiv (m / n)
  send smod (m % n)
.
```

Same flexibility as in `div_mod_server`

## Tensor(`⊗`/`[]`): You have to be ready for any processing order

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

* `s[sdiv,smod]` and the `recv` can commute.
* The two `send` must be in parallel.

## Forwarders

If we have a channel `c` following a session `S` and a channel `d` following
session `~S` (the dual of `S`) and for which `c` and `d` are
allowed to be used together, then one can define a process forwarding data
back and forth between `c` and `d`.

For instance, let have the session `S` be `!Int.?Int.?Int`.

```
fwd_send_recv_recv (c : !Int.?Int.?Int, d : ?Int.!Int.!Int) =
  recv d (x : Int)
  send c x
  recv c (y : Int)
  send d y
  recv c (z : Int)
  send d z
.
```

Since forwarding works for any session and can easily be automated, the language
has a built-in construct called `fwd`:

```
fwd_send_recv_recv_auto (c : !Int.?Int.?Int, d : ?Int.!Int.!Int) =
  fwd(!Int.?Int)(c,d)
.
```

The forwarders are actually more flexible than this, not only data can be
forwarded back and forth but it can also be duplicated and forwarded to listeners
on the side. Consider the previous example where one adds one listener `e`:

```
fwd_send_recv_recv_with_listener (c : !Int.?Int.?Int,
                                  d : ?Int.!Int.!Int,
                                  e : ?Int.?Int.?Int) =
  recv d (x : Int)
  send c x
  send e x
  recv c (y : Int)
  send d y
  send e y
  recv c (z : Int)
  send d z
  send e z
.
```

Or using the `fwd` construct:

```
fwd_send_recv_recv_with_listener_auto (c : !Int.?Int.?Int,
                                       d : ?Int.!Int.!Int,
                                       e : ?Int.?Int.?Int) =
  fwd(!Int.?Int.?Int)(c,d,e)
.
```

## Additives

(not yet supported in the prototype)

```
A₀ ⊕ A₁ = !(x : 𝟚). case x 0: A₀ 1: A₁
A₀ & A₁ = ?(x : 𝟚). case x 0: A₀ 1: A₁
0       = !(x : 𝟘). λ()
⊤       = ?(x : 𝟘). λ()
```

## Loli

```
A -o B = {~A,B}
A -o B -o C -o D
  = {~A,B -o C -o D}
  = {~A,{~B,C -o D}}
  = {~A,{~B,{~C,D}}}
  ≃ {~A,~B,~C,D}
```

## `{}`/`[]` are associative and commutative

```
{A,B} -o {B,A}
[A,B] -o [B,A]
```

## `[::]` is associative

```
[:[:A,B:],C:] -o [:A,[:B,C:]:]
```

## Mix rule

```
[A0,...,An] -o {A,...,An}

[] -o {}
[A,B] -o {A,B}
```

##

```
A : Session.
B : Session.
C : Session.
ten_loli_par (c : [A,B] -o {A,B}) =
  c{i,o}
  i{na,nb}
  o{a,b}
  (fwd(A)(a,na) | fwd(B)(b,nb))
.
par_comm_core (i : ~{A,B}, o : {B,A}) =
  i[na,nb]
  o{b,a}
  (fwd(A)(a,na) | fwd(B)(b,nb))
.
par_comm (c : {A,B} -o {B,A}) =
  c{i,o}
  @par_comm_core(i,o)
.
ten_comm (c : [~B,~A] -o [~A,~B]) =
  c{i,o}
  @par_comm_core(o,i)
.
par_assoc_core (i : ~{{A,B},C}, o : {A,{B,C}}) =
  i[nab,nc] nab[na,nb] o{a,bc} bc{b,c}
  (fwd(A)(a,na) | fwd(B)(b,nb) | fwd(C)(c,nc))
.
par_assoc (c : {{A,B},C} -o {A,{B,C}}) =
  c{i,o}
  @par_assoc_core(i,o)
.
ten_assoc (c : [[~A,~B],~C] -o [~A,[~B,~C]]) =
  c{i,o}
  @par_assoc_core(o,i)
.
ten_loli_seq (c : [A,B] -o [:A,B:]) =
  c{i,o}
  i{na,nb}
  o[:a,b:]
  (fwd(A)(a,na) | fwd(B)(b,nb))
.
par_loli_seq (c : {A,B} -o [:A,B:]) =
  c{i,o}
  i[na,nb]
  o[:a,b:]
  (fwd(A)(a,na) | fwd(B)(b,nb))
.
seq_assoc_core (i : ~[:[:A,B:],C:], o : [:A,[:B,C:]:]) =
  i[:nab,nc:]
  nab[:na,nb:]
  o[:a,bc:]
  bc[:b,c:]
  (fwd(A)(a,na) | fwd(B)(b,nb) | fwd(C)(c,nc))
.
seq_assoc (c : [:[:A,B:],C:] -o [:A,[:B,C:]:]) =
  c{i,o}
  @seq_assoc_core(i,o)
.
```

##

### Rejected

```
{A,B} -o [A,B]
```

### Should be accepted eventually

```
{!S,!T} -o [!S,!T]
{?S,?T} -o [?S,?T]
[:[:A,B:],C:] -o [:A,[:B,C:]:]
[:A,[:B,C:]:] -o [:[:A,B:],C:]
```

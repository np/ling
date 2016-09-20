# Ling: Programing with linear types, a tutorial

This is a tutorial for [Ling] language. Concepts, constructs and idoms are
introduced through a series of examples.

---

## What to expect from this tutorial?

This tutorial is a guided tour of the language using short examples
of increasing complexity.

### Summing an array of integers

By the end of this tutorial, this process which is reads an array
and writes back its sum, should look less intimidating:

```{.haskell}
sum_int = proc(a : {?Int ^ 10}, r : !Int)
  new/alloc (acc :* Int).
  acc <- 0.
  split acc as [: acci ^ 10, accn :].
  split a   as {  ai   ^ 10 }.
  sequence ^ 10 with i (
    let x : Int <- ai.
    let y : Int <- acci.
    acci <- (x + y)
  ).
  fwd(?Int)(accn, r)
```

On the process above, the compiler yields the following `C` program:

```{.c}
void sum_int(const int a[10], int *r) {
  int acc;
  acc = 0;
  for (int i = 0; i < 10; i = i + 1) {
    const int x = a[i];
    const int y = acc;
    acc = x + y;
  };
  const int z = acc;
  *r = z;
}
```

### Enforcing parallelism and sequencing with types

By the end of this tutorial  these funny looking types should be more
instructive on how they enforce the program behavior of this process which
reads to two integers and write back their division and modulus.

```{.haskell}
div_mod_server = proc(c : [: [?Int, ?Int], [!Int, !Int] :])
  c[:r,s:]
  r[rm,rn]
  s[sdiv,smod]
  ( recv rm (m : Int)
  | recv rn (n : Int)).
  ( send sdiv (m / n)
  | send smod (m % n))
```

## The basics: processes, actions, channels, sessions, terms and types

The language of processes is the core specificity of [Ling], but here
is a short description of each syntactic category of the language:

* **Processes** compute by acting on channels.
* **Actions** on channels include sending and receiving data, but also channel
  allocation and splitting.
* **Channels** must be used linearly, namely each expected action
  should be done and only once.
* **Sessions** are types for channels, not only describe the shape of
  what data gets exchanged but can precisely describe in what order data
  gets exchanged.
* **Terms** are used to describe what has a type and a permanent value,
  namely processes, sessions, and types themselves.
* **Types** are used to type terms and are terms themselves.
  Syntactically, types and terms are mixed. The distinction between types
  and terms happens through type-checking, namely a type is a term which
  has the type `Type`.

Here are a few examples:

* A process: `proc(i : ?Int, o : !Int) recv i (x : Int). send o (i + i)`
* Actions: `recv i (x : Int)`, `send o (i + i)`
* Channels: `i` and `o` above.
* Sessions: `?Int` (receive an integer), `!Int` (send an integer)
* Terms: `(i + i)`, but also processes, sessions and types are terms.
* Types: `Int`, `Proc(i : ?Int, o : !Int)` (which is the type of the process
  above)

## One language, two views: Memory Access and Message Passing

Processes, actions and channels can also be regarded from a “shared memory
access” view point. Processes become procedures, actions become statements,
and channels become memory locations. Actions such as `recv` and `send` become
`read` and `write`, finally channel allocation become memory allocation.

Unlike traditional concurrency libraries implemented on top of shared memory,
we can use a language which natively supports parallelism, sequencing and
concurrency to write programs accessing a shared memory and not necessarily
using a multi-core architecture.

**Why such nonsense⁈** simply because we get a class of programs much more
amenable to reasoning both on its functionality and performances.

For instance, given a process written in [Ling] one can automatically derive
the total amount of memory required and the number of reads and writes to the
these memory locations.

Moreover [Ling] supports a class of cost-free abstractions through the used
of fused channels. In particular this enables to write programs using high
level abstractions and retain a clear knowledge of the required resources.

## Send and receive: atomic sessions

### A first example

We start with a "doubling server" which receives one integer `n` on the channel
`rn` (`r` stands for `receive`), and *then* sends `n + n` on the channel `sdbl`
(`s` stands for `send`).

```{.haskell}
double_server = proc(rn : ?Int, sdbl : !Int)
  recv rn   (n : Int).
  send sdbl (n + n)
```

The *session* type for the channels indicates the protocol to follow on such
channel. For any type `A` (such as `Int`), the session `?A`, means to receive
an `A` and the `!A` means to send an `A`.

The *process* is then made of two actions here. The action `recv c (x : A)`
receives on the channel `c` and then _binds_ the received _term_ to the
_variable_ `x`. The action `send c t` sends on the channel `c` the term `t`.

When running processes in a closed _term context_ the terms being communicated
may first be evaluated as _values_.

### Signatures

The types of _definitions_ such as `+` and types `Int` are given as a
_signature_. For now let's assume the following signatures:

~~~{.haskell}
Int : Type
_+_ : (m : Int)(n : Int) -> Int
_/_ : (m : Int)(n : Int) -> Int
_%_ : (m : Int)(n : Int) -> Int
~~~

## Channel allocation and parallel composition

How to use our doubling server. The following process has one given channel
`sdbl` on which it should send an `Int`. To do so one first allocate a new
channel which introduces two endpoints: `rn` and `sn`. Then one describe
two processes which are composed in parallel `(P | Q)`. On the left a reference
to our doubling server which should receive on `rn` and send on `sdbl`. On
the right the process sends the value `21` on the channel `sn`. Since `rn` and
`sn` are the two endpoint of the same channel, sending `21` on `sn` is received
on `rn`, then bound as `n`, the send action is then ready to send `21 + 21`
hence `42`.

~~~{.haskell}
double_21 = proc(sdbl : !Int)
  new [rn : ?Int, sn : !Int]
  ( @double_server(rn, sdbl)
  | send sn 21)
~~~

The reference to a previous defined process is equivalent to substituting the
definition in place of the reference, potentially renaming the channel names
to match the ones in the reference. Here is the previous example, expanded:

```{.haskell}
double_21_expanded = proc(sdbl : !Int)
  new [rn : ?Int, sn : !Int]
  ( recv rn   (n : Int).
    send sdbl (n + n)
  | send sn 21)
```

The semantics of `double_21(s)` is equivalent to `send s 42`.

More generally the process
`new [r : ?A, s : !A] (recv r (n : A). P | send s t. Q)`
is equivalent to the process
`(P[n := t] | Q)` where one substitutes `t` for `n` in `P`.

The parallel composition of processes is commutative and associative which
is a quite important property as it preserves typing in our language.

More formally for all processes `P`, `Q`, and `R`,
`(P|Q)` is equivalent to `(Q|P)` and `(P|(Q|R))` is equivalent to `((P|Q)|R)`.

One can thus compose processes with no particular nesting: `(P|Q|R|S)`.

TODO: remark about the potential need of synchronisation when using `new`,
because a key feature of [Ling] is that we can avoid synchronisation in a
large class of cases.

### Sending two results

Our next example is a simple server to compute division and modulus of two integers.
In contrast to functional programming there is no need to package the two results
as a single one using a tuple. This might look like an imperative
program where two addresses are given to write the two results instead of
"returning" them. The good news is that the theory behind it makes these
processes a lot more functional that they look like and thus they enjoy similar
properties.

```{.haskell}
div_mod_server_simple = proc(rm : ?Int, rn : ?Int, sdiv : !Int, smod : !Int)
  recv rm (m : Int).
  recv rn (n : Int).
  send sdiv (m / n).
  send smod (m % n)
```

### Receiving and sending in parallel

Exchanging the order of the two `recv` actions yields to a different process.
Similarly with exchanging the `send` actions.
However here one can compose them in parallel:

```{.haskell}
div_mod_server_explicit_prll = proc(rm : ?Int, rn : ?Int, sdiv : !Int, smod : !Int)
  ( recv rn (n : Int)
  | recv rm (m : Int)).
  ( send sdiv (m / n)
  | send smod (m % n))
```

Notice here that we still need one use of the sequencing operator `.`.
Otherwise `m` and `n` would not be available for the `send` actions.

## Continued sessions: imposing a strict processing order

So far a channel was given a session such as `?Int` or `!Int`, namely
a single action to be performed. [Ling] supports richer sessions were
one can make a continued use of a channel for several actions. For
instance, the example below receives two integers on the channel and then
sends back two integers again on the same channel:

```{.haskell}
div_mod_server_cont = proc(c : ?Int.?Int.!Int.!Int)
  recv c (m : Int).
  recv c (n : Int).
  send c (m / n).
  send c (m % n)
```

You might wonder how this might work without synchronisation, indeed we need
two slots in the memory. The compiler can implement the session
`?Int.?Int.!Int.!Int` with only two integers, which will both get read and
then both be written.

## Sequences(`»`/`[::]`): Fixed, left-to-right processing order

TODO: description

```{.haskell}
div_mod_server_seq4 = proc(c : [: ?Int, ?Int, !Int, !Int :])
  c[:rm,rn,sdiv,smod:]
  recv rm (m : Int).
  recv rn (n : Int).
  send sdiv (m / n).
  send smod (m % n)
```

No flexibility. It has to be in this order.

## Par(`⅋`/`{}`): You control the processing order!

TODO: description

```{.haskell}
div_mod_server_par4 = proc(c : {?Int, ?Int, !Int, !Int})
  c{rm,rn,sdiv,smod}
  recv rm (m : Int).
  recv rn (n : Int).
  send sdiv (m / n).
  send smod (m % n)
```

Same flexibility and possible variations as in `div_mod_server`

## Tensor(`⊗`/`[]`): You have to be ready for any processing order

TODO: description

```{.haskell}
div_mod_server_par2_ten2_ten2 = proc(r : [?Int, ?Int], s : [!Int, !Int])
  r[rm,rn]
  s[sdiv,smod]
  ( recv rm (m : Int)
  | recv rn (n : Int)).
  ( send sdiv (m / n)
  | send smod (m % n))
```

* The two `recv` must be in parallel.
* The two `send` must be in parallel.

However the type does not forces the `recv`s to happen before the `send`s.

```{.haskell}
fake_div_mod_server_ten2 = proc(r : [?Int, ?Int], s : [!Int, !Int])
  r[rm,rn]
  s[sdiv,smod]
  ( send sdiv 42
  | send smod 21).
  ( recv rm (m : Int)
  | recv rn (n : Int))
```

Combining a sequence type and tensors we get:

```{.haskell}
div_mod_server_seq2_ten2_ten2 = proc(c : [: [?Int, ?Int], [!Int, !Int] :])
  c[:r,s:]
  r[rm,rn]
  s[sdiv,smod]
  ( recv rm (m : Int)
  | recv rn (n : Int)).
  ( send sdiv (m / n)
  | send smod (m % n))
```

This type rules out `fake_div_mod_server_ten` and is the best simple type for
it has it enforce the maximum amount of parallelism.

## Forwarders

If we have a channel `c` following a session `S` and a channel `d` following
session `~S` (the dual of `S`) and for which `c` and `d` are
allowed to be used together, then one can define a process forwarding data
back and forth between `c` and `d`.

For instance, let have the session `S` be `!Int.?Int.?Int`.

```{.haskell}
fwd_send_recv_recv_manually = proc(c : !Int.?Int.?Int, d : ?Int.!Int.!Int)
  recv d (x : Int).
  send c x.
  recv c (y : Int).
  send d y.
  recv c (z : Int).
  send d z
```

Since forwarding works for any session and can easily be automated, the language
has a built-in construct called `fwd`:

```{.haskell}
fwd_send_recv_recv_auto = proc(c : !Int.?Int.?Int, d : ?Int.!Int.!Int)
  fwd(!Int.?Int.?Int)(c,d)
```

The forwarders are actually more flexible than this, not only data can be
forwarded back and forth but it can also be duplicated and forwarded to listeners
on the side. Consider the previous example where one adds one listener `e`:

```{.haskell}
fwd_send_recv_recv_with_listener_manually =
  proc(c : !Int.?Int.?Int,
       d : ?Int.!Int.!Int,
       e : !Int.!Int.!Int)
  recv d (x : Int).
  ( send c x
  | send e x).
  recv c (y : Int).
  ( send d y
  | send e y).
  recv c (z : Int).
  ( send d z
  | send e z)
```

Or using the `fwd` construct:

```{.haskell}
fwd_send_recv_recv_with_listener_auto =
  proc(c : !Int.?Int.?Int,
       d : ?Int.!Int.!Int,
       e : !Int.!Int.!Int)
  fwd(!Int.?Int.?Int)(c,d,e)
```

TODO explain the `Fwd <Nat>` type and `fwd <Nat>` construct

[Ling]: https://github.com/np/ling

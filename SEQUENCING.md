How to deal with arbitrary sequencing?
======================================

## Motivation

An example where this comes up in practice is when
you want to log about a message your sending:

```
send dest m
send log "Sending #{m} to #{dest}"
```

However both sends are currently independent.
On the receiving side we can enforce some sequencing, consider:

```
send log "Waiting a message on #{dest}..."
recv dest (m : Int)
send log "Received #{m} from #{dest}"
```

In this example the second `send` cannot go before the `recv` because of
the variable m being used. However the first `send` can go past the `recv`:

```
recv dest (m : Int)
send log "Waiting a message on #{dest}..."
send log "Received #{m} from #{dest}"
```

Which was not the intended behavior. Notice that the first `send` cannot
go past the second one since they are on the same channel.

## Proposal

One can wonder about the consequences of permitting action sequencing.

One could write `send c M. P` when sequencing is required (same with recv).

Additionally to this explicit sequencing we should provide a way to express
explicit parallelism, namely:

We could write `(a0 | ... | aN). P` to mean `a0 ... aN. P`
when all `ai` channels are distinct.
Since they are distinct any permutation of the `ai` is congruent to
`(a0 | ... | aN). P`.

Let's consider a concrete example, with the following protocol:
  `(c : ?Int.!Int, d : ?Int.!Int)`

What we have now, implicit parallelism/sequencing:

```
proc1 (c : ?Int.!Int, d : ?Int.!Int) =
  recv c (x : Int) recv d (y : Int)
  send c (x + y)   send d (x * y)
```

Equivalent version with explicit sequencing and implicit parallelism:

```
proc2 (c : ?Int.!Int, d : ?Int.!Int) =
  recv c (x : Int) recv d (y : Int).
  send c (x + y)   send d (x * y)
```

Equivalent version with explicit sequencing and explicit parallelism (my favorite):

```
proc3 (c : ?Int.!Int, d : ?Int.!Int) =
  (recv c (x : Int) | recv d (y : Int)).
  (send c (x + y)   | send d (x * y))
```

Additional sequencing which yields the same result but as a non-equivalent process:

```
proc4 (c : ?Int.!Int, d : ?Int.!Int) =
  recv c (x : Int). recv d (y : Int)
  send c (x + y)    send d (x * y).
```

There is in total 8 configurations (the middle dot is implicit):

* ?c.?d!c!d  or ?c.?d!d!c
* ?d.?c!c!d  or ?d.?c!d!c
* ?c?d!c.!d  or ?d?c!c.!d
* ?c?d!d.!c  or ?d?c!d.!c
* ?c.?d!c.!d
* ?d.?c!c.!d
* ?c.?d!d.!c
* ?d.?c!d.!c

What does sequencing imply:

* Neither a `send` nor a `recv` can go past a `.`
* Since these nested `send`, `recv` must be in par I see
  no reason to choose the sequencing (or paralellism)
* Sequencing should not stop the spliting of arrays (pars, tensors, sequences)
  I guess this was the original reason to avoid the dots.
  For instance, this process `send c 4. e{f,g} P` causes trouble as we might
  need it in this form `e{f,g} send c 4. P` to perform the cut.
  I see two ways to alleviating this problem:
  (A) allow splits to go across dots
  (B) forbid splits under dots
  I think the best situation for the theory is (A), but in practice
  enforcing (B) seems clearer since the theory (A) will be oblivious to it.

## Sequencing of arbitrary processes

So far sequencing is used between the prefix and the tail of parallel
processes.

A further extension would allow `P.Q`, however I don't no how to deal
with processes such as `(P | Q).R` in general.

Amongst the simplest examples:

```
(send c 1. send d 2 | send e 3. send f 4). send g 5
```

Question: Are received messages scoping beyond the dot?
* If not, is this powerful enough?
* If so, this makes the

In a way, if one ignores the splits (or consider they are done eagerly), typing
`P.Q` could be similar to `P|Q` with

We'll delay this extension while gathering more examples.

## Implementation

* Syntax: A process can now take an optional sequencing dot
  between the prefix and the parallel tail:
  `π .? (P0 | ... | PN)`
* Check: enforce condition (B) above.
  In `π . (P0 | ... | PN)`, first check `(P0 | ... | PN)` to get `Δ`.
  Then check that `Δ` does not have any head sessions for arrays
  (pars, tensors, sequences), then proceed checking `π`.
* Syntax: A prefix can now take this form `(a0 | ... | aN)`
* Check: `(a0 | ... | aN)` should be off distinct channels.
  Remark: if we desugar this parallel prefix into an implicitly
  parallel prefix we risk to introduce captures (the same issue
  apears in the sequencing transformation) unless we enforce
  non-shadowing.
* Warning: try to warn about potential misuse of the implicit
  sequencing/parallelism
* Warning/Check: warn about variable shadowing.
  One reason is the following corner case
  `(recv c (x : Int) | send d x)`,
  it might be confusing that the second `x` is NOT an
  occurrence of the first `x`.

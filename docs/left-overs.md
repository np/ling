# TODO unfinished bits

TODO: I guess that most of this should take part of the Reference Manual.

## Additives

(not yet supported in the prototype, see [Issue#10](https://github.com/np/ling/issues/10))

```{.haskell}
A₀ ⊕ A₁ = !(x : LR). case x of { `left -> A₀ ; `right -> A₁ }
A₀ & A₁ = ?(x : LR). case x of { `left -> A₀ ; `right -> A₁ }
0       = !(x : Empty). case x of {}
⊤       = ?(x : Empty). case x of {}
```

## Loli

Definition:

```{.haskell}
A -o B = {~A,B}
```

Equivalences:

```{.haskell}
A -o B -o C -o D
  == A -o (B -o (C -o D))
  == {~A,B -o C -o D}
  == {~A,{~B,C -o D}}
  == {~A,{~B,{~C,D}}}
  ~= {~A,~B,~C,D}
  ~= {{~A,~B,~C},D}
  == {~[A,B,C],D}
  == [A,B,C] -o D
```

## `{}`/`[]` are associative and commutative

```{.haskell}
{A,B} -o {B,A}
[A,B] -o [B,A]
```

## `[::]` is associative

```{.haskell}
[:[:A,B:],C:] -o [:A,[:B,C:]:]
```

## Mix rule

```
[A0,...,An] -o {A,...,An}

[] -o {}
[A,B] -o {A,B}
```

| Session        | Parallel           | Sequential                 |
|----------------|--------------------|----------------------------|
| [A,B] -o {A,B} | ten_loli_par.ll    | ten_loli_par_sequential.ll |
| {A,B} -o {B,A} | par_comm.ll        |

```
A : Session
B : Session
C : Session

par_comm_core = proc(i : ~{A,B}, o : {B,A})
  i[na,nb]
  o{b,a}
  (fwd(A)(a,na) | fwd(B)(b,nb))

par_comm = proc(c :
  c{i,o}
  @par_comm_core(i,o)

ten_comm = proc(c : [~B,~A] -o [~A,~B])
  c{i,o}
  @par_comm_core(o,i)

par_assoc_core = proc(i : ~{{A,B},C}, o : {A,{B,C}})
  i[nab,nc] nab[na,nb] o{a,bc} bc{b,c}
  (fwd(A)(a,na) | fwd(B)(b,nb) | fwd(C)(c,nc))

par_assoc = proc(c : {{A,B},C} -o {A,{B,C}})
  c{i,o}
  @par_assoc_core(i,o)

ten_assoc = proc(c : [[~A,~B],~C] -o [~A,[~B,~C]])
  c{i,o}
  @par_assoc_core(o,i)

ten_loli_seq = proc(c : [A,B] -o [:A,B:])
  c{i,o}
  i{na,nb}
  o[:a,b:]
  (fwd(A)(a,na) | fwd(B)(b,nb))

par_loli_seq = proc(c : {A,B} -o [:A,B:])
  c{i,o}
  i[na,nb]
  o[:a,b:]
  (fwd(A)(a,na) | fwd(B)(b,nb))

seq_assoc_core = proc(i : ~[:[:A,B:],C:], o : [:A,[:B,C:]:])
  i[:nab,nc:]
  nab[:na,nb:]
  o[:a,bc:]
  bc[:b,c:]
  (fwd(A)(a,na) | fwd(B)(b,nb) | fwd(C)(c,nc))

seq_assoc = proc(c : [:[:A,B:],C:] -o [:A,[:B,C:]:])
  c{i,o}
  @seq_assoc_core(i,o)
```

### TODO: Rejected

```
{A,B} -o [A,B]
```

### TODO: Should be accepted eventually

```
{!S,!T} -o [!S,!T]
{?S,?T} -o [?S,?T]
[:[:A,B:],C:] -o [:A,[:B,C:]:]
[:A,[:B,C:]:] -o [:[:A,B:],C:]
```

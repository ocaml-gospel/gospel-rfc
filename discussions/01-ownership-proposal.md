
## Questions and Approaches in the Literature

When one wishes to specify the behavior of an imperative program using
preconditions and postconditions (collectively referred to as *assertions*),
two questions arise:

* Should assertions be *formulae* in some logic,
  or *expressions* in a subset of the programming language?
  If the former, which logic? If the latter, which subset?

* Should assertions be allowed to *dereference* a mutable location,
  that is, to *read* the value stored at this location?

In **Hoare Logic**, with **mutable global variables** only, assertions are
formulae, and can refer to expressions, which in turn can read a global
variable. In addition to a precondition and a postcondition, a specification
must indicate which global variables are affected. (When the code is known,
this information is syntactically evident.)

In **Hoare Logic** still, once **dynamic memory allocation** is introduced,
one can think of the store as a large array, stored in a single distinguished
global variable. This might work in principle; yet in practice, because
(almost) every function modifies the store, this forces the user to explicitly
describe in the postcondition the relation between the initial and final
stores. This in turn forces the user to explicitly reason about disjointness,
freshness, etc., and seems intolerable. To remedy this, one can introduce more
fine-grained memory models, where the store is simulated by several arrays
stored in several distinct global variables; this can be done, e.g., on a
per-field or per-type basis (following Burstall's 1972 paper), or based on a
region analysis. This may relieve some of the pain, but remains unpleasant, as
it still sometimes requires the user to reason about disjointness, freshness,
sets of (un)modified locations, etc. In this approach, it is still permitted
for an assertion to read a mutable location in the store, but (as a downside)
it is difficult to tell which assertions are preserved or invalidated by a
function call.

**Separation Logic** (SL) attempts to remedy this problem by removing the
possibility for an assertion to dereference a location in the store, unless
(at the same time) this assertion claims the unique ownership of this
location. The points-to assertion `r ↦ v` simultaneously claims the unique
ownership of the location `r` and asserts that the value currently stored at
this location is `v`. The logical interpretation of the separating conjunction
connective `∗` is designed so that it is impossible to own a location twice:
as a result, the conjunction `r1 ↦ v1 ∗ r2 ↦ v2` implies `r1 ≠ r2`. This leads
to a logic where every assertion is *stable*, that is, cannot be invalidated
by a participant other than the owner of this assertion. In other words, this
leads to a logic where the *frame rule* is valid. Yet in other words, this
leads to a logic where the specification of a function consists of just a
precondition and a postcondition: there is no need for a `modifies` clause.
This seems very pleasant and desirable. Yet, a downside is that this leads to
a style where assertions are quite obviously formulae, *not* programs. There
is no way for an assertion to *read* a memory location: dereferencing is not
part of the syntax of formulae. Instead, the user is led towards a style based
on *binary predicates*, which relate an OCaml value (typically the address of
a data structure) with a mathematical value (typically the logical model of
this data structure). The points-to predicate for references, `r ↦ v`, is an
example; it could also be written `isRef(r, v)`. More generally, when dealing
with an abstract data type, say, a queue, one is usually lead to introducing
an abstract predicate `isQueue(q, Q)`, where `q` is the address of the queue
and `Q` is the logical model of the queue (the sequence of elements held in
the queue). This style requires a universal quantification over the auxiliary
variable `Q`, and can feel somewhat alien to a programmer.

**Implicit Dynamic Frames** (IDF) is presented by its authors as a variant of
Separation Logic that seems more natural to programmers. In IDF, the points-to
assertion is split into two components. On the one hand, the assertion
`acc(r)` represents the unique ownership of the reference `r`. This assertion
intuitively means that `r` can be accessed: it is a permission to read and
write `r`. On the other hand, expressions are allowed to read the heap, so
(for instance) the assertion `!r = v` claims that the value currently stored
at address `r` is `v`. The points-to assertion of SL, `r ↦ v`, is encoded as
the conjunction `acc(r) ∗ !r = v`. An attractive feature of this approach is
that it is possible to refer to the content of the reference `r` directly as
`!r`, without introducing a name `v` for this value. Similarly, if `q` is a
queue, then a *unary predicate* `isQueue(q)` asserts that the queue is valid
(and claims its unique ownership), while the logical model of the queue is
denoted by the expression `view q`, where `view` is a logical function; there
is no need to introduce an auxiliary variable `Q`. This relies on the fact
that expressions (and logical functions) can read the heap. A downside of this
approach is that not every assertion is stable under interference, or
*self-framing*: whereas `acc(x)` or `isQueue(q)` are stable, `!r = v` or `view
q = Q` are not stable. This makes it difficult to define the meaning of
assertions and to develop a verification system based on IDF. (Parkinson
and Summers do propose a definition of the meaning of assertions; however,
it is not simple.)

The **Gospel** specification language, **as it stands today**, requires just a
precondition and a postcondition. (For simplicity, let me first discuss the
special case where every argument is listed in the `modifies` clause.) Even
though Gospel assertions do not explicitly express ownership assertions, every
mutable argument or result is implicitly assumed to be uniquely (separately)
owned. Thus, Gospel can be viewed as syntactic sugar for SL; the desugaring
process is type-directed. Thus, if an argument `r` has type `int ref`, for
instance, then the desugared precondition requires `r ↦ _`. If, furthermore,
the precondition requires `!r ≥ 0`, then the desugared precondition requires
`∃v.( r ↦ v ∗ v ≥ 0 )`.

## Strengths and Weaknesses of Gospel

The strengths of Gospel's current notation are as follows:

* Ownership and disjointness claims are implicit,
  so the common case where the arguments must be owned and disjoint
  is easy to describe.

* The logical model of a data structure is denoted through a functional
  notation, such as `!r` or `view q`. Thus,
  + there is no need for an auxiliary variable `v` or `Q`;
  + a logical expression, such as `!r`,
    looks similar to an OCaml expression, such as `!r`.

There are some areas where I perceive the definition of Gospel as unclear or
limited. (I have had some difficulty spelling out these areas, which may be a
good sign.) They are are as follows:

* It is not clear how to describe **a value without a permission**. For
  example, it is not clear how to indicate that a function argument is not
  owned.

  This limitation is often tolerable in an `.mli` file, because concrete
  mutable objects are usually presented as inhabitants of an abstract type
  `T`, which is (implicitly?) accompanied with an abstract Separation Logic
  predicate `isT`, whose definition is not given in the `.mli` file. Then, the
  problem of indicating that an argument of type `T` is not owned can be
  viewed as the problem of giving a suitable definition of the predicate
  `isT`. This moves the problem from the `.mli` file to the `.ml` file. (This
  is the case in the specification of Union-Find in the Gospel paper, where
  elements have abstract type `elem`, and where the Separation Logic predicate
  `isElem` does not imply unique ownership of the underlying mutable object.)
  This approach does not always work, though: some functions, like
  `Array.blit`, require arguments that have a concrete type yet are not
  (separately) owned. Furthermore, inside an `.ml` file, the problem still
  stands: there is no way of indicating that a function argument or a record
  field is not owned.

* It is not clear how to describe **a permission without a value**.

  This limitation can perhaps also be tolerated in an `.mli` file, as follows:
  if a function needs a permission that is not associated with any of its
  arguments, then a ghost argument can be added, and the necessary permission
  can be associated with this ghost argument. (This is the case in the
  specification of Union-Find in the Gospel paper, where the functions take a
  ghost argument `uf` of abstract type `uf_instance`; the owership of the
  shared state can then be described by the Separation Logic predicate
  `isUfInstance` which is associated with this type.) However, inside an `.ml`
  file, the problem still stands: to define the predicate `isUfInstance`, we
  need a way of claiming the ownership of a location (or a set of locations).

* The **logical reflection of values** is not clearly defined. If `x`
  has type `int ref` or `int array` or `int ref array`, what kind of
  mathematical value is denoted by `x` when this variable is used in
  a logical assertion? Is it just a memory location, or is it a
  deeper (more structured) value?

* The **implicit association between OCaml types and Separation Logic
  predicates** is not clearly defined. When an OCaml function takes an
  argument `q` of type `_ Queue.t`, this means that its precondition (once
  desugared) contains `isQueue(q, _)`. We should clarify whether the
  Separation Logic predicate `isQueue` must be declared, how many parameters
  it takes, and whether the association between the type `_ Queue.t` and the
  predicate `isQueue` must be declared. We should check that this association
  is compatible with type equalities: if the type `t` is defined as an alias
  for the type `u`, then the predicates `isT` and `isU` should be equivalent.
  We should clarify how this association interacts with the module system.
  We should clarify how this association interacts with polymorphism: is
  every OCaml type implicitly associated with a representation predicate?
  Should the function `view` be polymorphic (overloaded)?
  Is it permissible to refer to `view x` when `x` has type `'a`?
  Should the logical model of a queue be *the sequence of the elements*
  of the queue, or *the sequence of the logical models of the elements*
  of the queue?

* The status of **the logical functions that read the heap**, such as `!` and
  `view`, is not clear. Although they are disguised as logical functions, in
  reality, they seem to be sugar for parameters of the representation
  predicate: for example, `view q` is sugar for `Q`, in the presence of the
  assertion `isQueue(q, Q)`. We should clarify the connection between logical
  functions and representation predicates. In particular, if we wish to give
  syntax for recursive definitions of logical functions that read the heap,
  then we should clarify that this syntax desugars to inductive definitions of
  representation predicates (which implies that there is no need to require
  the definitions to be well-founded!).

## A Proposal

We want to keep the strengths of Gospel described above, namely:
* a functional notation for logical models, such as `!r` and `view q`;
* ownership and disjointness by default;
* a logical interpretation of formulae
  that is defined by desugaring them into Separation Logic.

I propose to view `!` and `view` as **pseudo-functions** which in apparence
are allowed to read the heap, but, in reality, are sugar for metavariables
accompanied with side conditions expressed in Separation Logic.

Let's use examples to see how this might work. (Note: I am temporarily
ignoring the problems caused by the fact that several objects have the same
name, such as `!` in OCaml code and `!` in Gospel formulae.)

Suppose, for now, that references are the only primitive mutable objects.
I propose to deal with references as follows:

* A reference of type `'a ref` in OCaml has type `'a ref` in Gospel.
  This logical type is understood as a synonym for (or a subset of)
  the type `loc` of all memory locations.
  Its inhabitants are memory locations.
* So, if `r` has type `'a ref` in OCaml,
  then `r` has type `'a ref` in Gospel,
  and denotes an address.
* The Separation Logic predicate `isRef(r, v)`,
  also written `r ↦ v`,
  claims the unique ownership of the reference at address `r`
  and guarantees that its content is the value `v`.
  It is never explicitly used in Gospel specifications;
  I am using it only to explain how Gospel pseudo-functions
  are desugared.
* The Gospel pseudo-function `!` has type `'a ref -> 'a`
  and is defined as follows:
  + `!r` denotes `w` provided `isRef(r, w)` holds.

* Uses of pseudo-functions are expanded as follows.
  A use of `!r` is desugared to a fresh
  variable `w` and that `∃w. isRef(r, w) ∗ ...` is introduced as
  close as possible to the site where `r` is bound. Multiple uses
  of `!r` are desugared to multiple uses of the same variable `w`, and a single copy
  of the assertion `∃w. isRef(r, w) ∗ ...` is introduced.
* The OCaml primitive operations on references have the following
  Gospel specifications:
  ```
    val ref: 'a -> 'a ref
    (*@ r = ref v
          ensures !r = v *)

    val (!): 'a ref -> 'a
    (*@ v = !r
          ensures !r = v *)

    val (:=): 'a ref -> 'a -> unit
    (*@ r := v
          modifies r
          ensures !r = v *)

    val (==): 'a ref -> 'a ref -> unit
    (*@ b = (r1 == r2)
          ensures b = true ↔ r1 = r2 *)
  ```

Let us examine how these specifications are desugared into Separation Logic.

* For `ref`, the use of `!r` in the postcondition is replaced with a
  fresh variable `w` together with the assertion `isRef(r, w)`, so we
  obtain:
  ```
    { True } ref v { r. ∃w. isRef(r, w) ∗ w = v }
  ```
  which is equivalent to:
  ```
    { True } ref v { r. isRef(r, v) }
  ```

  (When a pseudo-function is used inside an equation, one can usually
  avoid the introduction of a fresh variable `w` and use the term on
  the other side of the equation instead. In the following, I will do
  so directly.)

  (One should note that `r` is the result of the function, not an argument,
  so there is no question as to whether `isRef(r, _)` should appear in the
  precondition as well.)

* For `(!)`, the use of `!r` in the postcondition means that `isRef(r, _)`
  must be introduced in the postcondition. Because `r` is a parameter of the
  function, this means (by convention?) that `isRef(r, _)` must also be
  introduced in the precondition. Furthermore, the absence of a `modifies`
  clause means that an equality should be introduced (or, the same variable
  should be used) in the postcondition so as to reflect the fact that the
  logical model of `r` does not change. Thus, we get:
  ```
    { isRef(r, w) } !r { v. isRef(r, w) ∗ w = v }
  ```

* For `(:=)`, as before, the use of `!r` in the postcondition means that
  `isRef(r, _)` must be introduced in the pre- and postcondition. This time
  there is a `modifies` clause, so no equality is introduced to relate the
  pre- and post- states. We get:
  ```
    { isRef(r, w1) } r := v { _. ∃w2. isRef(r, w2) ∗ w2 = v }
  ```
  that is:
  ```
    { isRef(r, _) } r := v { _. isRef(r, v) }
  ```

* For `(==)`, the absence of uses of `!r1` and `!r2` means that there is
  no need to introduce `isRef(_, _)`. Thus, there is no ownership or
  disjointness requirement. We get:
  ```
    { True } r1 == r2 { b. b = true ↔ r1 = r2 }
  ```
  The mathematical equality `r1 = r2` is interpreted as an equality
  between two memory locations.

## Area Under Construction

The following points should be discussed:

* How to model mutable objects; per-object versus per-field ownership.

* Name collisions and name spaces.

* The meaning of (the presence or absence of) `modifies` clauses in Gospel.
  When absent, how do they desugar into fractional permissions or
  read-only permissions or equalities between input and output views?
  Are they type-directed? What is their extent, that is, how deep does
  the read-only area extend?

* The use of iterated conjunction in a predicate definition (e.g., Union-Find).
  How to expand a pseudo-function application `!r` when `r` is bound by an
  iterated conjunction.

* Definitions of recursive pseudo-functions, which are interpreted
  as inductive Separation Logic predicates, without the need to
  prove well-foundedness.

# Context for the proposal

## Motivation

Gospel currently makes the following assumptions regarding mutable data
structures and aliasing:

- different values (of a mutable type) are always disjoint in memory
- having access to a (mutable) value means having full recursive access to its contents

Limitations:

- fine-grained pointer reasoning
  + without sharing: mutable linked lists
  + with sharing: union find

- nesting mutable data structures (`int array array`, `int ref list`, etc)
  + appears via polymorphism
  + appears via record fields

## Goal

Extend gospel to be able to reason about fine-grained aliasing and ownership

Design constraints: be a "conservative" generalization of current gospel

- good defaults: cases that can already be handled are *specified the same* as
  they are now

- current gospel specifications are seen as *sugar* for more fine-grained
  notions involving aliasing and ownership

- no "discontinuity": one can freely mix "sugar" with more fine-grained
  primitives; one does not need to switch to a completely different
  specification language when needing to reason about aliasing/ownership

## Key ideas

- reuse solutions proposed in the context of Separation Logic

- introduce a distinction between holding a program value (e.g. the location of
  an array) and having ownership over it, having *access* to its contents (e.g.
  the contents of the array)
    
- extend gospel with a way of specifying the "extent of ownership" considered
  for a given value

- new *spatial assertions* `x @ r`. `r` is a *representation predicate*
  describing the extent of ownership associated with value `x`.

- By default, each ocaml type comes with a default `r` asserting recursive
  ownership (access to the value and its contents).


# Current status of the proposal

- what works well
  + functions specifications (syntax, spatial clauses, etc)
  + base types (ref, array, etc), pure types, abstract types
  + record types with mutable fields
  + group ownership
  + ownership for ghost types/arguments/return values

- points to discuss
  + syntactic convention for lifting ocaml types to gospel types

- what doesn't work so well
  + temporarily extract an element from a container (`Array.get`)

- what is WIP
  + syntax on the implementation side (.ml files) to define representation
    predicates
  + syntax for defining alternative representation predicates for existing ocaml types

- to be worked on later
  + a way to have several specifications for a function?
  + some form of "borrowing"
  + some form of read-only permissions

# Example: stack

A mutable stack that owns its elements:

```ocaml
(* this is stack.mli *)

type 'a stack
(*@ model 'a seq *)

val length : 'a stack -> int
(*@ n = length s
      consumes s @ 'a stack
      produces s @ 'a stack, n @ int
      ensures n = Seq.length s
*)

val create : unit -> 'a stack
(*@ s = create ()
      ensures s = Seq.empty
*)

val push : 'a stack -> 'a -> unit
(*@ push s x
      modifies s
      consumes x
      ensures s = old x :: old s
*)

val pop : 'a stack -> 'a
(*@ x = pop s
      modifies s
      requires s <> []
      ensures old s = x :: s
*)
```

# Example: references

```ocaml
(* this is ref.mli *)

(* This assumes that we have the following, in the gospel logic:
   - A gospel type 'a &ref of reference values, as abstract locations
   - A gospel type for the logical model of a reference:
     type 'a ref = { contents : 'a }
   - A gospel logical function to lookup the contents of a ref model:
     function (!) r = r.contents
*)

val ref : 'a -> 'a ref
(*@ r = ref v
      ensures !r = v
*)
   (* desugars into: *)
(*@ r = ref v
      preserves v @ 'a
      produces r @ 'a ref
      ensures !r = v
*)

val (!): 'a ref -> 'a
(*@ v = !r
      ensures !r = v
*)
  (* desugars into: *)
(*@ v = !r
    preserves r @ 'a ref
    produces v @ 'a
    ensures !r = v
*)

val (:=): 'a ref -> 'a -> unit
(*@ r := v
      modifies r
      ensures !r = v
*)
  (* desugars into: *)
(*@ r := v
      preserves r @ 'a ref, v @ 'a
      modifies r
      ensures !r = v
*)

val (==) : 'a ref -> 'a ref -> unit
(*@ b = (r1 == r2)
      preserves r1 @ any, r2 @ any
      ensures b = true <-> r1 = r2 *)
```


# Syntactic categories

**Existing**:
- ocaml types
- ocaml values
- gospel types
- gospel terms

**New**:
- *representation predicates*

Representation predicates follow the same syntax as ocaml types: there are
(polymorphic) representation predicates `'a ref`, `'a array`, `'a list`, etc.
(where `'a` is a *representation predicate variable*)


# Liftings

- ocaml type -> gospel type
  + for pure types, an equivalent gospel type in the logic
  + for mutable types, a type of "shallow program values" (e.g. locations)
  
- ocaml value -> gospel term
  + the type of the gospel term is the lifting of the ocaml type

- ocaml type -> default representation predicate
  + describes ownership over values of this type


# Representation predicates

A representation predicate relates two *gospel* types: implementation and model

Typically:
- the implementation type corresponds to the lifting of an ocaml type
- the model type is a mathematical structure (sequences, sets, etc)

Examples of *representation predicates* for base types:
- `int`: relates machine integers and mathematical integers (?)
- `'a array`: relates a gospel type of locations and mathematical sequences
- `'a list`: relates a mathematical list of implementations for `'a` with a
  mathematical list of models for `'a` (`'a` is a representation predicate
  itself)

Special representation predicate not associated with an ocaml type: `any`
- asserts no ownership
- relates any implementation type to itself
- is in fact a *class* of representation predicates, parameterized by
  the implementation type (the implicit parameter is always inferred)


# Syntactic conventions and liftings

For each ocaml type we need two gospel types:
- the gospel types of *values* of this type
- the gospel type of their *mathematical model* according to the default
  representation predicate

Proposal: for an ocaml type `t`, we have gospel types:
- `t` for the mathematical model (may be manually defined as an alias of the
  relevant type of a mathematical structure)
- `&t` for the type of values (`&` should be seen as part of the type name)


For each ocaml type, we need a default representation predicate.

Proposal: the default representation predicate of an ocaml type `t` is also named `t`.

# Functions specifications

4 base clauses:
- spatial clauses: `consumes`/`produces`
- functional/pure clauses: `requires`/`ensures` (as before)


The `consumes`/`produces` clauses describe ownership and have the format:
```
  consumes x @ t, y @ t', ...
  produces r @ t'', ...
```

- sugar: `modifies` means `consumes` and `produces`
- sugar: one can write `x` for `x @ t`, when `t` is the default representation
  predicate for `x` of OCaml type `t`.
- (sugar or extension: `preserves` requires read-only access)
- sugar: if nothing is said about an argument, then it is `preserved`
         if nothing is said about a result then it is `produced`
         
         
The `requires`/`ensures` clauses are logical Gospel formulae.
They can contain:
- `x` which refers to the *model* of `x` as described by the representation predicate
- `&x` which refers to the *value* of `x` (lifted as a gospel term)
- `old e` where `e` is a gospel expression that can include the terms above

NB: `old (&x) = &x` always!


# Records

```
type t = { mutable foo : int; bar : int array }
```

- corresponding gospel type for the model: same record where the type of the
  fields corresponds to the model for full ownership

- default representation predicate `t`: full ownership over the record

- additionally, one can write `x.foo @ ...`, `x.bar @ ...` for
  *per field* ownership
- in clauses requires/ensures, `x.foo`, `x.bar` consequently refer to
  the model of that field; `&(x.foo)` is not allowed because the
  location of a record field is not a first class value in OCaml

- there is no direct way of expressing "the ownership of the record cell".
  The way to do this is require shallow per-field ownership of every field:
  `x.foo @ any, x.bar @ any`. We think this is an acceptable limitation.

- it should be possible to also associate an invariant with the
  record definition; establishing `x @ t` requires proving the invariant


# Abstract types

## when no model is provided

```ocaml
type t
```

(Q: if nothing is specified, is `t` assumed to be ephemeral or persistant?)

- generate an abstract gospel type `t` for the model

## with model fields

```ocaml
type t
(*@ model capacity : int *)
(*@ mutable model contents : int seq *)
(*@ invariant Seq.length contents <= capacity *)
```

- generate a gospel type `type t = { capacity : int; contents : int seq }` for
  the model
- additionally, allow `x.capacity @ ...`, `x.contents @ ...` for per-field ownership

## (extension) whole model

Proposed extension

```ocaml
type t
(*@ model : int seq *)
```

- the model is directly `int seq`
- (the representation predicate `t` thus relates `&t` and `int seq`)


# Ghost arguments / return values

(XXX Current proposal, but has issues wrt naming; needs more thinking)

- some gospel types can have an associated default representation predicate
- by default, passing them as ghost arguments requires the associated ownership
- if a gospel type used as a ghost argument does not have an associated
  representation predicate, no ownership is required (equivalent to using `any`
  as the representation predicate)

# Group ownership

(XXX Needs more thinking to solidify this as a proper instance of a general
  mechanism of "ghost types with ownership" *)

Example with union-find:

```ocaml
type 'a elem
(*@ duplicable *)

(*@ type 'a uf
  model dom : 'a elem set
  model rep : 'a elem -> 'a elem
  model img : 'a elem -> 'a
  invariant ... *)

val make : 'a -> 'a elem
(*@ e = make [uf: 'a uf] v
      consumes v
      modifies uf
      ensures not (mem e (old uf.dom)) /\ ...
*)
```

- `'a uf` is a gospel logical type with associated ownership
  and default representation predicate

- passed as ghost parameter of e.g. `make`


- more generally, we should be able to define the interface for a 
  generic ghost theory of group ownership (TODO)


# Polymorphic functions and containers


# Module system


# Defining representation predicates for type declarations


# Defining multiple representation predicates for the same OCaml type


# @pure functions

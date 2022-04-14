# Reflections on integers, machine integers, abstract types, and subset types

The issue of modeling integers in Gospel is somewhat subtle and tricky,
because of the distinction between machine integers and ideal (mathematical)
integers, and because of our desire to hide this distinction wherever possible.

Naturally, this problem arises in just about every specification and
verification system, not just Gospel, so a review of the related systems
would be useful here, but is missing for now.

## Can machine integers be viewed as an abstract type in OCaml and Gospel?

Because machine integers are a primitive type (a very important one!), we can
and may be tempted to invent all sorts of ad hoc solutions to this issue. Yet,
I think it is interesting to step back and **ask how machine integers could be
treated if they were an ordinary OCaml abstract type**, provided by a library,
instead of a primitive type. Would we be able to write a satisfactory Gospel
specification for them? If the answer is positive, then this may suggest an
natural way of dealing with machine integers. If the answer is negative, then
this may point to a shortcoming of Gospel.

So, let us assume that

* Ideal integers are available in Gospel formulae,
  including ideal integer literals such as `42`
  and ideal integer operations such as addition `+`, multiplication `*`, and so on.

* The type `int` is not primitive, but is an abstract type,
  provided by an OCaml module `Int`,
  whose specification we need to write.

The signature of the module `Int` would be something along the following lines:

```
module Int : sig
  type int
  val zero : int
  val one : int
  val min_int : int
  val max_int : int
  val add : int -> int -> int
  val mul : int -> int -> int
  (* ... and many more operations ... *)
end
```

What might be the specification of this module in Gospel?
**Several specifications** come to mind: for example, we might
wish to disallow integer overflows; or, we might wish to
allow them and specify two's complement arithmetic; or,
we might think of a third specification where a machine integer
is modeled as a fixed-length sequence of bits.
For now, let us assume the former.

A Gospel specification along the following lines comes to mind:

```
(*@ function min_int : integer *)
(*@ function max_int : integer *)
(*@ axiom pos_max_int: 0 <= max_int *)
(*@ axiom range: -min_int = max_int + 1 *)

(*@ predicate representable (i : integer) =
      min_int <= i && i <= max_int      *)

module Int : sig

  type int
  (*@ model view: integer
      invariant representable view *)

  val zero : int
  (*@ ensures view zero = 0 *)
  val one : int
  (*@ ensures view one = 1 *)
  val min_int : int
  (*@ ensures view min_int = min_int *)
  val max_int : int
  (*@ ensures view max_int = max_int *)

  val add : int -> int -> int
  (*@ z = x + y
      requires representable (view x + view y)
      ensures view z = view x + view y *)

  val mul : int -> int -> int
  (*@ z = x + y
      requires representable (view x * view y)
      ensures view z = view x * view y *)

end
```

The ideal integers `min_int` and `max_int` are axiomatized at the level of
Gospel. (We may wish to go further and define them as `-2^w` and `2^w-1`
where `w` is the word length minus one.) The axiom `range` uses Gospel's
operations on ideal integers as well as the ideal integer literal `1`.

The predicate `representable` indicates which ideal integers can be
represented by a machine integer. Its definition is concrete.

The type `int` is treated as an OCaml abstract type.
The model of a machine integer is an ideal integer,
so a `view` function of type `int -> integer` is declared.
The view of a machine integer is always a representable integer,
so a data type invariant is declared: `representable view`.

The OCaml constants `zero`, `one`, `min_int`, `max_int` receive
specifications that specify their views. (Incidentally, there is
a name clash between OCaml's `min_int` and Gospel's `min_int`.)

The specification of addition requires that the result be representable, and
guarantees that the view of the result is the sum of the views of the
arguments.

Some remarks:

* The types `int` and `integer` both exist at the level of Gospel,
  but `int` is an abstract type,
  so one cannot do anything with a variable `i` of type `int`
  except apply the function `view` to it.

* Because the type `int` is equipped with a data invariant,
  as soon as a variable `i` of type `int` is in scope,
  the assumption `representable (view i)` should automatically
  be brought into scope as well.
  In fact, as soon as a logical expression `e` has type `int`,
  the assumption `representable (view e)` should automatically appear.
  For instance, if `xs` is a Gospel sequence of type `int seq`,
  then `representable (view s[0])` should automatically be
  considered true.
  Indeed, it would be painful if exploiting a data invariant
  was an explicit operation.

* Writing `i.view` or `view i` is of course extremely heavy.
  It seems desirable to allow `view` to be declared as a coercion,
  if possible. Yet, this can create ambiguity in some places.
  For instance, `view x = view y` is an equation between ideal integers.
  If we allow writing `x = y` instead, then it is unclear whether we
  mean `view x = view y`, an equation at type `integer`,
  or `x = y`, an equation at type `int`.

* What is the meaning of equality at an abstract type anyway?
  I suppose that (in general) it should be unspecified.
  At type `int`, we could specify that it is extensional:
  ```
    (*@ axiom extensionality: view i = view j -> i = j *)
  ```
  On the one hand, this should not be essential: we should always
  be able to avoid using equality at type `int`, if we so wish.
  On the other hand, it could be a way of stating that the
  ambiguity mentioned above is not problematic: the equations
  `view i = view j` and `i = j` are equivalent.

* Viewing `int` as an abstract type (both at the OCaml level and at the Gospel
  level) implies that there are no literals of type `int` (at either level).
  This is problematic in practice.

  At the level of OCaml, ad hoc support for integer literals could be added as
  follows. If a literal such as `42` appears in OCaml code, then the program
  verification system could view it as an abstract object `i` accompanied with
  the hypothesis `view i = 42`.

  At the level of Gospel, I would be tempted to say that literals of type
  `int` should never be needed. However, as pointed out by Paul today (April
  8, 2022), if a data type `distance` has been declared in OCaml by
  `type distance = D of int`, then the data constructor `D` has type
  `int -> distance` both in OCaml and in Gospel,
  so `D 42` in Gospel is ill-typed (ouch!)
  and it is not entirely clear how this object should be written.

* In fact, by viewing `int` as an abstract type,
  we fail to express the idea that *every ideal integer `i` such that
  `representable i` holds is represented by some machine integer*.
  We might express this fact by declaring
  ```
    (*@ function represent (i : integer) : int *)
    (*@ axiom round_trip: representable i -> view (represent i) = i *)
  ```
  I note that if `i` has type `int` then `representable (view i)` holds
  so (by the above axiom) `view (represent (view i)) = view i` holds,
  which (by extensionality) implies `represent (view i) = i`. So, the
  round-trip property in the reverse direction holds as well.

* So, in Gospel, `42` has type `integer`,
  and `represent 42` has type `int`.
  This is notationally heavy, but principled.
  One can invent an ad hoc notation for it if desired,
  such as `42i`, proposed by Paul.

## Conclusion

In the end, I think that, even though I have tried to start from scratch, I
have converged towards (almost?) exactly the same point where Gospel currently
lies.

* There is a distinction between `int` and `integer` in Gospel,
  and there is one in this proposal as well.
  This cannot be avoided if we accept the premise that *every OCaml type
  is also a Gospel type*.

* There is a coercion from `int` to `integer` in Gospel,
  and there is one in this proposal as well.
  (It is initially named `view`, but using it explicitly seems too heavy.)

* The type `int` in Gospel can be viewed as a concrete type, which denotes a
  subset of the integers. Instead, I propose viewing `int` in Gospel as an
  abstract type, equipped with a data invariant `representable view`. The
  distinction is blurry: these concepts seem to be essentially the same. In
  both cases, if `i` has type `int` then `42 <= i` is a valid formula and is
  an inequation between the ideal integer `42` and the ideal integer `view i`.

* In both cases, (I think) the mathematical operations (such as `+`) and
  relations (such as `=` and `<=`) are defined only at type `integer` and
  there is never a need to use them at type `int`. This seems desirable, as
  this allows us to avoid overloading and potential ambiguity.

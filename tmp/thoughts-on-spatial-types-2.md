list:
- things that work
  + functions specifications (general case, examples that work well: push/pop on stack, ...)
- things that don't work so well
  + temporarily extract an element from a container (`Array.get`) ("borrowing"): for later.
  + ownership for records
- things to debate
  + syntactic convention for lifting ocaml types to gospel types

syntactic categories/namespaces:
------
- ocaml types
- ocaml values
- gospel types
- gospel terms
- spatial assertions (right now we never have spatial assertion identifiers, only concrete spatial assertions)
- representation predicates (every rep. pred. has two arguments)


syntactic meta-functions assumed by the system
------
- `lift_ty` : ocaml type -> gospel type
- `lift_term` : ocaml value -> gospel term
- `ty_rpred` : ocaml type -> representation predicate
- `rpred_impl_ty` : representation predicate -> gospel type (*!!*)
- `rpred_model_ty` : representation predicate -> gospel type
- `own_at` : *gospel* term -> representation predicate -> spatial assertion
  (a gospel term (instead of an ocaml term) on the LHS makes this also useful for ghost parameters)
- `own_impl` : spatial assertion -> gospel term
- `own_model` : spatial assertion -> gospel term

such that:
- if `|- v : t` in OCaml then `|- lift_term(v) : lift_ty(t)` in Gospel
- for `t` an ocaml type, `rpred_impl_ty(ty_rpred(t)) = lift_ty(t)`
- `own_impl(own_at(x, R)) = x`
- if `|- x : t` in OCaml, `own_at(lift_term(x), R)` is only well formed if `rpred_impl_ty(R) = lift_ty(t)`
- `|- own_model(own_at(x, R)) : rpred_model_ty(R)` in Gospel

- `lift_ty` distributes over parameterized types: `lift_ty(int ref) = lift_ty(int) lift_ty(ref)`
  The type `_ lift_ty(ref)` is in fact a type of memory locations
  and its parameter is a phantom parameter (its purpose is only to
  prevent the user from mixing different types of locations by mistake).
- `lift_ty` distributes over products and sums: `lift_ty(t1 * t2) = lift_ty t1 * lift_ty t2` etc.
  (i.e. pure OCaml types are lifted (redefined) at the level of gospel)
- `lift_ty(t)` corresponds to the Gospel type of the (syntactic) values that
  have OCaml type `t`. `lift_ty(int ref)` is a Gospel type that corresponds to
  memory locations (Gospel equality on values of this type corresponds to `(==)`
  on the corresponding OCaml values). `lift_ty(int list)` is the Gospel type of
  pure lists of integers, and `lift_ty(int ref list)` corresponds to a Gospel
  list of memory locations. (NB: `lift_ty(int array)` and `lift_ty(int ref)` are
  Gospel types that behave similarly, but are different types and are not
  interchangeable.)
- `lift_ty` is injective


functions specifications
--------

4 base clauses:
- spatial clauses: `consumes`/`produces`
- functional/pure clauses: `requires`/`ensures` (as before)

The `consumes`/`produces` clauses describe ownership and have the format:
```
  consumes own_at(lift_term(x), R), own_at(lift_term(y), R'), ...
  produces own_at(lift_term(x), R), own_at(lift_term(y), R'), ...
```

- sugar: `modifies` means `consumes` and `produces`
- sugar: one can write `own(lift_term(x))` for `own_at(lift_term(x), ty_rpred(t))` for `|- x : t` in OCaml
- sugar, or extension: `preserves` requires read-only access
- sugar: if nothing is said about an argument, then it is `preserved`,
         if nothing is said about a result then it is `produced`

The `requires`/`ensures` clauses are logical Gospel formulae.
They can contain:
- `lift_term(x)`
- `own_model(own_at(lift_term(x), _))` where the representation predicate is inferred from the spatial clauses
  (this assumes that there is only one assertion `own_at(lift_term(x), ...)`)
- `old e` where `e` is a gospel expression that can include the terms above
- NB: `old (lift_term(x)) = lift_term(x)` always!


syntactic conventions and liftings
-------

Proposal: for an ocaml type `t`, we have gospel types:
- `t` for the mathematical model (may be manually defined as an alias of the
  relevant type of a mathematical structure)
- `&t` for the type of values (`&` should be seen as part of the type name)

interaction de & et polymorphisme:
  "&('a ref)" := 'a &ref

  autrement dit, le paramètre de type sur un &foo correspond à une variable de
  type fantôme, qui correspond au type contenu dans le type conteneur
  correspondant à ce type addresse. On l'utilise pour éviter de mélanger des
  addresses qui correspondraient à différents types ocaml

  &'a &ref existe aussi, mais correspond à un type de ref différent : le type des
  locations de &'a ref


concrete representation predicates
--------

## representation predicates not associated with an ocaml type

any, group (?, depends whether it is exposed as an ocaml value)

## base types

int, ref, array, list

## pure types

ADTs and records with no mutable fields

## records with mutable fields

```
type t = { mutable foo : int; bar : int array }
```

it would be nice to be able to talk about `x.bar` without having ownership over `x`; since the field is not mutable it can be aliased freely. Generally speaking, do we want per-field ownership or full-record ownership?

-----

we need a grammar of representation predicates that just describe the ownership of the record cell.
this doesn't neatly match with the syntax of ocaml types anymore like previously, where we would exploit the fact that recursive ownership would occur for polymorphic occurences (for containers)
here we have recursive ownership for fields with monomorphic types (even non mutable ones, as long as there is a mutable field in the record)

repr predicate: `{ foo : ?; bar : ? }` <- schema of rpreds?

idea: structural records for representation predicates, while keeping nominal records for gospel types?
  -> Problem: what are `rpred_impl_ty` et `rpred_model_ty` for a structural rpred ??
  -> at best we can imagine defining a compatibility relation with nominal gospel types, but no direct lifting
  -> seems bad overall

pour un type ocaml `t` record, on pourrait définir deux rpreds, un appelé `t`
(`ty_rpred(t)`) pour la possession récursive, et un appelé `t_cell` pour la
possesion shallow du record seul.... mais comment exprimer le fait que `t_cell`
n'est pas un vrai rpred polymorphe ?
en fait, quelles sont exactement les contraintes de type ?

-> contraintes sur le type de gauche (qui doit être `lift_ty(t)` après composition récursive des rpreds)

```
rpred ('a, 'b) t_cell = { foo : 'a; bar : 'b }
  constraint rpred_impl_ty('a) = int
         and rpred_impl_ty('b) = int array

rpred t = (int, int array) t_cell

rpred_impl_ty(('a, 'b) t_cell) = t (?)
rpred_impl_ty(t) = t
rpred_model_ty(('a, 'b) t_cell) = ?
```

need two gospel types? one for the shallow cell and one for the deep cell? impl/model?
  -> more complicated than that bc of iterated recursive ownership

record type with at least one mutable fields
-> impl gospel type ~= loc
-> model gospel type = ? type paramétré de record, avec un paramètre de type par champ (mutable ou non(!)) ?
  un peu moche..


ou alors: mécanisme similar à `any`, où on a une classe de rpreds avec désambiguation dirigée par les types ocaml
  afin d'avoir des rpreds record structurels, associés à des types nominaux
  type impl OK en utilisant le type ocaml
  type model -> ?
    quand même besoin d'un type record gospel, dont les champs auront des types différents selon le rpred
      (ou famille de types record gospel)

ou alors, juste sucre syntaxique:

```
(* types gospel *)
type ('a, 'b) t_cell = { foo : 'a; bar : 'b }

instance du type: (integer, int list) t_cell

avec sucre: { foo : integer; bar : int list } ?
(* Q: au niveau des termes on peut utiliser les types pour désambiguer, mais comment faire au niveau des types ? *)

(foo: integer, bar: int list) t_cell ?
{ foo : integer; bar : int list } as t_cell ?

(* est-ce qu'on peut avoir ce sucre de manière systématique pour tous les types record gospel,
   ou est-ce qu'il faut maintenir une DB séparée des types "à la" t_cell ? *)
```

--------
Better solution:

```
type t = { mutable foo : int; bar : int array }
```

- defines a representation predicate `ty_rpred(t)` which corresponds
  to full, recursive ownership over the record. (Recall that this is
  the default representation predicate for `t`.)

- defines two gospel types:
  + `lift_ty(t)` (corresponds to a type of locations)
  + a gospel record type (TODO: name/lifting function?) for the model
    associated with `ty_rpred(t)` (ie it is
    `rpred_model_ty(ty_rpred(t))`); here, e.g. 
    `type t_model = { foo : integer; bar : int seq }`

- allows writing per-field spatial assertions of the form 
  `x.foo @ ...`, `x.bar @ ...`. They represent the ownership over a 
  single field of the record

- in clauses requires/ensures, `x.foo`, `x.bar` consequently refer to
  the model of that field; `&(x.foo)` is not allowed because the
  location of a record field is not a first class value in OCaml

- when using per-field representation predicates, one can refer to
  `&x` in requires/ensures clauses, but not `x` (!), only per-fields
  models e.g. `x.foo`.

- when using `x @ ty_rpred(t)` (the default representation predicate
  for full recursive ownership of the record), one can use `&x`, `x`
  (with the usual meaning), and `x.foo`, `x.bar` work as well by the
  fact that `x` denotes a gospel record (the model).


--------

on veut pouvoir associer un invariant à une définition de record, même dans un .mli

exemple de stack avec capacity (immutable), length (mutable), list items (mutable)
inv:    length < capacity
inv:    length = length(items)
inv:    capacity >= 0



record pur + invariant ??
  -> ne peut pas devenir un record "normal" gospel
  -> car on veut pouvoir déduire que les champs satisfont l'invariant
  -> type abstrait gospel?

on a besoin de type record gospel + invariant pour décrire le modèle de records
mutables pour le prédicat de représentation par défaut qui prend possession
récursive


------

```
type t = { mutable foo : int; bar : int array }
```

après désucrage
```
x @ t

x.foo @ int
= "x @ int .foo" ? (moralement? + syntaxe x.foo dans requires/ensures)

x.bar @ int seq
= "x @ int seq .bar" ?
```


après traduction en SL

```
type &t := loc
type t := { foo : int; bar : int seq } (* 'a array = 'a seq *)

rpred T (x: &t) (v: t) :=
  x ~> {{ foo ; bar }} *
  Int foo v.foo *
  Array Int bar v.bar

rpred .Foo (A: rpred &a a) (x: &t) (v: a) :=
  x ~> {{ foo; .. }} *
  A foo v

rpred .Bar (A: rpred &a a) (x: &t) (v: a) :=
  x ~> {{ ..; bar }} *
  A bar v

lemma unfold:  T x v  *--*  .Foo Int x v.foo * .Bar (Array Int) x v.bar
```

semble ok, tant qu'il n'y a pas deux records avec des champs du même nom dans le scope
  dans ce cas, il faut disambiguer, basé sur les types ocaml ?


## ADTs (with constructors with mutable fields)

...


# génération automatique de noms

où?

```
val f : a -> b
  r = f x
    consumes x @ a
    produces x @ a, r @ b

~> introduit x:a, r:b, &x:&a, &r:&b dans la logique (pre/post)
```

```
type t
(*@ x : t
      model : int seq
      invariant  ... x ... *)
~> x : int seq
```

NB: `model int seq` désirable anyawy pour éviter .view partout / par cohérence
avec comment les rpreds fonctionnent en général
nécessite le header `x:t`, mais on en a besoin anyway (TODO check why)

```
type t
(*@ x : t
      model foo : int
      mut model bar : int seq
      invariant ... x.foo .. x.bar ... (?) *)
~> x:t, x.foo:int, x.bar:int seq
```

<-> incohérence: quelle version choisir? <->

```
(??)
type t
(* model foo : int
   mut model bar : int seq
   invariant ... foo .. bar ... *)
~> foo:int, bar:int seq
```


```
(*@ x : t  with model foo  ?
    x : t  as foo ?
*)

type t
(*@ x : t as seq
      model int seq
      invariant len seq >= 42 *)
```

```
allow, in a .ml?:

type t
(*@ x : t as foo
  owns x @ ...
  model : int seq = ..x..
or
  model foo : int seq = ..x..
*)
```

(not strictly needed, equalities can also be introduced by `invariant`)


donc: dans un .ml, pour définir un nouveau rpred:
```
type raw = { ... }

type t = raw
(*@ x : t as m
      model : int seq
      owns x @ raw
      invariant .. x .. m ..
*)
```

maintenant, quid du cas avec des champs modèle?
il faut spécifier pour chaque rpred de champ ce qu'il possède

```
type raw = { ... }

type t = raw
(*@ x : t as m
      model contents : int seq
      model capacity : int
      owns x @ raw
      owns capacity : x.foo @ int
      owns contents : x.bar @ int array
      invariant ...
      invariant capacity : ...
      .... ???
```

veut on un autre moyen que de définir un alias de type pour définir un nouveau
prédicat de représentation ?


representation predicates for abstract types
--------
way for the user to define the representation predicate associated with a type



duplicable/persistent aspect of representation predicates
--------

need to be able to specify that a representation predicate is duplicable or ephemeral
- for abstract types
- for polymorphic types/representation predicates in function specifications


polymorphic functions
--------


treatment of groups
-------


treatment of phantom arguments / return values
-------
- ghost arguments and return values do not exist at runtime, so they do not need
  to be OCaml values or to have OCaml types
- instead they can be directly Gospel values having Gospel types
- but a representation predicate is still needed, since we may need to talk
  about ownership associated with the ghost argument (of a group, for instance)

how do know the representation predicate to use by default ? we can't use
`ty_rpred` (this is for OCaml types), and we probably don't want to associate a
default representation to each *Gospel* type.

(----> have a `gty_rpred` that returns an option? and None is interpreted as meaning
  that we chose `any`)

ideas:
+ force the user to specify an explicit x @ ... for ghost arguments
+ or, by default, chose `any` for ghost arguments (but somewhat inconsistent w/ the
  default for normal arguments, and is the wrong default for types as `group`
  which are meant to carry ownership)
  [one could say that `group` should instead be a (dummy) real OCaml type, which
  gets us back the fact that the default interpretation carries ownership...
    but in general having representation predicates for logical types seems useful
    nonetheless]
+ have a typeclass-like (?) mechanism for associating a default representation
  predicate for even logical types
    exact workings of this mechanism? behavior/interaction with eg type aliases?..
    syntactic mechanism à la deriving X (introduce a bla_of function in scope /
    look up for such a function..)


proposal 1:
+ representation predicates/ownership are only associated with ocaml types
+ `group` must therefore be a dummy OCaml type
+ ghost arguments have type of syntactic class (gospel type | ocaml type)
  -> how do we distinguish between the two ?
    -> do ocaml/gospel types belong to distinct syntactic categories?
    -> or do we need to specify this in the syntax for ghost arguments?
+ if a ghost argument is of an ocaml type, it carries ownership (using the associated default representation predicate)
+ if a ghost argument is of a gospel type, it does not carry ownership
+ consequence, in the `union find` example, `type 'a uf` need to become a real OCaml type declaration

proposal 2:
+ have a sub syntactic category of logical-but-carrying-ownership gospel types
  -> subcategory of gospel types; logical-but-carrying-ownership types are gospel types
  -> but when used as ghost arguments, have a representation predicate associated
+ do we need new syntax to distinguish between `(*@ type 'a foo *)` when `foo` is a
  ghost-but-carrying-ownership type and when `foo` is a logical gospel type?
  * or it could just depend on whether one specifies a model when declaring the type
+ interaction with polymorphism at the level of gospel types: same question than for
  ocaml types (how do we interpret ownership of 'a?)
+ what does it mean for logical functions to operate on pure types that carry ownership?
  nothing particular, they just ignore the ownership aspect I guess and operate on them
  as normal logical values.
+ if `t` is an OCaml type, the representation predicate associated with
  `lift_ty(t)` (a gospel type) is `ty_rpred(t)`. This means using ghost
  arguments with ocaml types behaves as expected (the ghost argument carries the
  same ownership as if it was a normal argument of the function).


proposal:

- some gospel types can have an associated default representation predicate
- by default, passing them as ghost arguments requires the associated ownership
- if a gospel type used as a ghost argument does not have an associated
  representation predicate, no ownership is required (equivalent to using `any`
  as the representation predicate)

```ocaml
(*@ type t
      model int list *)
(* ~> declares a new default representation predicate for `t` *)
(* ~> which name? *)
(* ~> what about the case of a clash where there is already a 
    representation predicate named t because of an ocaml type t? *)


val f : unit -> unit
(*@ f [x: t] () 
      requires List.sum x = 42
*)
  (* desugars into *)
(*@ f [x: t] () 
      preserves x @ t
      requires List.sum x = 42
*)
```

- or, force the user to specify an explicit x @ .. for ghost arguments?
  but that doesn't solve the problem of *defining* the representation predicate


treatment of ghost function specifications
-------

```
(*@ val foo : a -> b
  requires ... / ensures ... / consumes ... / produces ...
*)
```

- corresponds to a "named" separation logic lemma
- all arguments/return values obey the same rule as ghost arguments
- thus the types of the arguments/return values of `foo` can be a mix of ocaml
  and gospel types


defining the representation predicate associated with a type in an implementation
-------

XXX TODO

```
(* in stack.ml *)
type t = { mutable size : int; mutable items : int array }
(*@ r : t
      model : int seq
      owns r @ { size : int; items : any },
           items @ int array

*)
```

need for a new declaration for associating ghost fields with an OCaml record type?
ghost fields could be used instead of exists quantifiers in the representation predicate



définir un prédicat de représentation pour un type existant
avec un alias de type (ghost?)
ou faut-il un nouveau mot clef ?


sur la stack, pouvoir définir une représentation pour le record avec la liste des items détachée
  pour pouvoir appeler la fonction length, sans préjuger de la possesion de la liste des éléments

et aussi pouvoir split la possession duplicable du champ capacity


# dans les .ml

```
(* dans stack.ml *)

type 'a t = {
  capacity : int;
  mutable length : int;
  mutable contents : 'a list
}
(*@ x : 'a t
      model { capacity : int; contents : (modelof 'a) seq }
      owns x.capacity @ int, x.length @ int, x.contents @ 'a list
      (* ou *) owns x.capacity, x.length, x.contents
      (* ou *) owns x.* (* ou rien? *)
      invariant x.length = Seq.length contents /\ Seq.length contents <= capacity /\ 0 < capacity
      invariant capacity = x.capacity /\ contents = Seq.of_list x.contents
*)
(* polymorphisme bizarre *)

type 'a open = 'a t
(* bof? *)
(*@ x : 'a open
      model { capacity : int; length : int; contents : 'a list }
      owns x.* @ any
*)

(*@ type 'a open = 'a t *)
(*@ model ... *)
(* ?? *)

(*@ repr 'a t_open 
    x : 'a t
     ....
  (syntaxe à déterminer)
*)

let mystack_broken : 'a open = { capacity = 0; length = 1; contents = [] }
let mystack_correct : 'a t = { capacity = 1; length = 0; contents = [] }

(*@ val close : 'a t -> unit
    () = close x
      consumes x @ 'a open, x.contents @ 'a list
      produces x @ 'a t
      requires x.length = List.length x.contents /\ List.length x.contents <= x.capacity /\ 0 < x.capacity
      ensures x.capacity = old x.capacity /\ x.contents = Seq.of_list (old x.contents)
*)

(* dans stack.mli *)
type 'a t
(*@ model { capacity : int; contents : 'a seq } *)
```


module system
-------

si on a un module OCaml M, avec m.mli qui contient des annotations

est-ce qu'on a nécessairement un module gospel M qui contient les déclarations
produites par les annotations de m.mli ?


mais alors, que faire du module Array de gospel vs le module Array de OCaml ?

idée: le module array de gospel c'est juste le module array de ocaml annoté
(avec juste un hack pour en avoir une version annotée)

si on veut des modules gospel spécifiques (par ex pour les théories pures),
alors on les mets dans un module Gospel (Gospel.Stdlib.XX ? ou Gospel.XX
directement ?) que l'on "possède" de toute façon dans le namespace global des
libs ocaml


attach a model to pure types
------

e.g. could we declare 'a seq as the model for 'a list


meaning of `pure` annotations
-------

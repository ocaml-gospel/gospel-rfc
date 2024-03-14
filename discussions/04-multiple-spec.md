The OCaml standard library proposes the `Queue` module to implement a
single-ended, FIFO data structure. For a reminder, here is a snippet of the
`queue.mli` file:

```ocaml
type !'a t
(** The type of queues containing elements of type ['a]. *)

exception Empty
(** Raised when {!Queue.take} or {!Queue.peek} is applied to an empty queue. *)

val create : unit -> 'a t
(** Return a new queue, initially empty. *)

val add : 'a -> 'a t -> unit
(** [add x q] adds the element [x] at the end of the queue [q]. *)

val take : 'a t -> 'a
(** [take q] removes and returns the first element in queue [q],
   or raises {!Empty} if the queue is empty. *)

val clear : 'a t -> unit
(** Discard all elements from a queue. *)

val iter : ('a -> unit) -> 'a t -> unit
(** [iter f q] applies [f] in turn to all elements of [q],
   from the least recently entered to the most recently entered.
   The queue itself is unchanged. *)

val transfer : 'a t -> 'a t -> unit
(** [transfer q1 q2] adds all of [q1]'s elements at the end of
   the queue [q2], then clears [q1]. It is equivalent to the
   sequence [iter (fun x -> add x q2) q1; clear q1], but runs
   in constant time. *)
```

From reading this interface, namely the type of `create` and `add` functions,
one can easily guess this is an ephemeral implementation of a Queue data
structure.

If we want to use Gospel to provide a formal specification to this interface, we
first provide type `t` with a ghost model field, as follows:

```ocaml
type 'a t
(* mutable model view: 'a sequence *)
```

Then, using the above `view` field, providing specification for the `queue`
functions (lets forget about `iter`, for now) is as easy as follows:

```ocaml
val create : unit -> 'a t
(*@ q = create ()
      produces q @ 'a t
      ensures q = nil *)

val add : 'a -> 'a t -> unit
(*@ add x q
      consumes q @ 'a t
      produces q @ 'a t
      ensures q = old q ++ [x] *)

val take : 'a t -> 'a
(*@ x = take q
      consumes q @ 'a t
      produces q @ 'a t
      raises Empty -> q = old q && q = nil
      ensures x :: old q = q *)

val clear : 'a t -> unit
(*@ clear q
      consumes q @ 'a t
      produces q @ 'a t
      ensures q = nil *)

val transfer : 'a t -> 'a t -> unit
(*@ transfer q1 q2
      consumes q1 @ 'a t
      consumes q2 @ 'a t
      produces q1 @ 'a t
      produces q1 @ 'a t
      ensures q1 = nil
      ensures q2 = old q2 ++ old q1 *)
```

Nothing of this is new; modulo the use of *spatial types*, this is the very same
example presented in Gospel's original FM'2019 paper (cf,
[here](https://inria.hal.science/hal-02157484/).

Now, the interesting part comes when one tries to prove the actual
implementation from `queue.ml`. For a reminder, here is the implementation of
the Queue data structure:

```ocaml
exception Empty

type 'a cell =
  | Nil
  | Cons of { content: 'a; mutable next: 'a cell }

type 'a t = {
  mutable length: int;
  mutable first: 'a cell;
  mutable last: 'a cell
}
```

and the corresponding functions:

```ocaml
let create () = {
  length = 0;
  first = Nil;
  last = Nil
}

let clear q =
  q.length <- 0;
  q.first <- Nil;
  q.last <- Nil

let add x q =
  let cell = Cons {
    content = x;
    next = Nil
  } in
  match q.last with
  | Nil ->
    q.length <- 1;
    q.first <- cell;
    q.last <- cell
  | Cons last ->
    q.length <- q.length + 1;
    last.next <- cell;
    q.last <- cell

let take q =
  match q.first with
  | Nil -> raise Empty
  | Cons { content; next = Nil } ->
    clear q;
    content
  | Cons { content; next } ->
    q.length <- q.length - 1;
    q.first <- next;
    content

let transfer q1 q2 =
  if q1.length > 0 then
    match q2.last with
    | Nil ->
      q2.length <- q1.length;
      q2.first <- q1.first;
      q2.last <- q1.last;
      clear q1
    | Cons last ->
      q2.length <- q2.length + q1.length;
      last.next <- q1.first;
      q2.last <- q1.last;
      clear q1
```

Since this modules implements queues as a recursive mutable type, it is out of
scope for the Cameleer tool. One can argue that it would be possible to derive a
small WhyML memory model for this implementation and then conduct the proof in
Why3. Indeed, and we have actually done it during VOCaL: [queue in
WhyML](https://github.com/ocaml-gospel/vocal/blob/main/proofs/why3/Queue_impl.mlw). More
on this later.

Let us use CFML, then. Assuming the OCaml implementation is in a file named
`Queue_OCaml.ml`, then the tool will produce a file named `Queue_OCaml_ml.v`
containing the characteristic formula for each function (this is not meant for
human consumption). Now, we focus on the actual proof of correctness, which we
put in the `Queue_OCaml_proof.v` file. As usual, we start with the
representation predicates:

```coq
Definition Cell A `{EA: Enc A} (v: A) (n c: cell_ A) : hprop :=
  \exists cf,
      \[c = Cons cf] \* (cf ~~~> `{ content' := v; next' := n }).

Fixpoint Cell_Seg A `{EA: Enc A} (L: list A) (to from: cell_ A) : hprop :=
  match L with
  | nil => \[to = from]
  | x :: L' => \exists n, (from ~> Cell x n) \* (n ~> Cell_Seg L' to)
  end.

Definition Queue A `{EA: Enc A} (L: list A) (q: loc) : hprop :=
  \exists (cf cl: cell_ A),
      (q ~~~> `{ length' := length L; first' := cf; last' := cl }) \*
        If L = nil then \[cf = Nil] \* \[cl = Nil]
        else
          \exists x L', \[L = L' & x] \* (cf ~> Cell_Seg L' cl) \*
                     (cl ~> Cell_Seg (x::nil) Nil).
```

There are a bunch of important lemmas on the defined representation predicates;
I will not show those here. We are now in position to specify and prove function
`clear`. Following the Gospel spec we provided in the interface, one might be
tempted to do the following in Coq:

```coq
Lemma Triple_clear : forall q L,
    SPEC (clear q)
      PRE (q ~> Queue L)
      POSTUNIT (q ~> Queue (@nil A).
```

And indeed, the proof follows. However, in the case `q` is a non-empty queue,
when the function returns one must prove that is sound to drop the ownership of
the representation predicate for fields `first` and `last`. In other words, one
must prove that these are affine predicates.

Now, the interesting part. We arrive to the proof of function `transfer`, whose
implementation we recall for the sake of readability:

```ocaml
let transfer q1 q2 =
  if q1.length > 0 then
    match q2.last with
    | Nil ->
      q2.length <- q1.length;
      q2.first <- q1.first;
      q2.last <- q1.last;
      clear q1
    | Cons last ->
      q2.length <- q2.length + q1.length;
      last.next <- q1.first;
      q2.last <- q1.last;
      clear q1
```

This function is specified in Coq as follows:

```coq
Lemma Triple_transfer : forall (L1 L2: list A) (q1 q2: loc),
    SPEC (transfer q1 q2)
      PRE (q1 ~> Queue L1 \* q2 ~> Queue L2)
      POSTUNIT (q1 ~> Queue (@nil A) \* q2 ~> Queue (L2 ++ L1)).
```

Let us focus on the case when `q1` is not empty but `q2` is the empty queue. For
such case, before the application `clear q1`, we are basically aliasing the
internal linked-list of `q1`. At such point, CFML will show (something similar
to) the following goal:

```coq
PRE (cl ~> Cell_Seg (x :: nil) Nil \*
     q2 ~~~> `{ length' := length (x0 & x); first' := cf; last' := cl} \*
     q1 ~~~> `{ length' := length (x0 & x); first' := cf; last' := cl} \* cf ~> Cell_Seg x0 cl)
CODE (App clear q1)
POST (fun _ : unit => (q1 ~> Queue nil \* q2 ~> Queue (x0 & x)) \* \GC)
```

Now, we *close* the representation of `q1` to get the following:

```coq
PRE (cl ~> Cell_Seg (x :: nil) Nil \*
     q2 ~~~> `{ length' := length (x0 & x); first' := cf; last' := cl} \*
     q1 ~> Queue (x0 & x)
CODE (App clear q1)
POST (fun _ : unit => (q1 ~> Queue nil \* q2 ~> Queue (x0 & x)) \* \GC)
```

and we can make the call `clear`, getting back

```coq
     q1 ~> Queue (@nil A)
```

This is the point where one gets stuck. We have lost the ownership of the
linked-list `cf` and `cl`. It is impossible to *close* the representation of
`q2` to get back a `Queue`.

The solution: change the specification of `clear`. Instead of re-using the
interface specification, use a more low-level specification, as follows:

```coq
Lemma Triple_clear_alt : forall (q: loc) (L1: list A) (x: A) (cf cl: cell_ A),
    SPEC (clear q)
      PRE (q ~~~> `{ length' := length (L1&x); first' := cf; last' := cl }
             \* cf ~> Cell_Seg L1 cl \* cl ~> Cell_Seg (x::nil) Nil)
      POSTUNIT (q ~> Queue (@nil A) \* cf ~> Cell_Seg L1 cl \*
                  cl ~> Cell_Seg (x::nil) Nil).
```

(*Note:* this is a spec that assumes the argument `q` is the non-empty
queue. Although not general, this is enough for our use case.)

The proof of the above spec is actually simpler than the previous one, no need
to prove that the predicates for `cf` and `cl` are affine. Getting back to the
proof of `transfer`, using the `Triple_clear_alt` lemma we are able to clear
`q1`. Since we now retain ownership of `cf ~> Cell_Seg L1 cl` and `cl ~>
Cell_Seg (x::nil) Nil`, we are able to *close* the representation of `q2` and
finish the proof of this case. The other cases of `transfer` follow, as well,
using the `Triple_clear_alt` spec.

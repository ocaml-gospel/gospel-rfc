module type STACK = sig

  (*@ predicate feasible (n : integer) *)

  (*@ axiom feasible_zero : feasible(0) *)

  (*@ axiom feasible_downward_closed :
        forall n1 n2. n1 <= n2 -> feasible(n2) -> feasible(n1) *)

  (*@ predicate maximal (n : integer) = not feasible(n+1) *)

  type 'a stack
  (*@ mutable model view: 'a seq *)
  (*@ invariant feasible(length(view)) *)

  (* NOTE The following predicate is a pseudo-predicate; it uses the
          pseudo-function [view] so it needs access to the content
          of the stack. *)
  (*@ predicate full (s : 'a stack) =
        maximal(length(view s)) *)

  val is_empty : 'a stack -> bool
  (*@ b = is_empty s
      ensures  b <-> s.view = empty *)

  val is_full : 'a stack -> bool
  (*@ b = is_full s
      ensures  b <-> full(s) *)

  val create : unit -> 'a stack
  (*@ s = create ()
      ensures  s.view = empty *)

  val push : 'a -> 'a stack -> unit
  (*@ push v s
      requires not full(s)
      modifies s
      ensures  s.view = cons v (old s.view) *)

  val pop : 'a stack -> 'a
  (*@ v = pop s
      requires 0 < length(s.view)
      modifies s
      ensures  old s.view = cons v s.view *)

end

(* In the following, we build a new STACK data structure by relying on
   two existing STACK data structures: [P] for parent, [C] for child.
   In a typical usage scenario, [P] would be an unbounded stack
   implemented as a reference to a linked list, while [C] would be a
   bounded stack implemented as a fixed-capacity array. The resulting
   data structure would be an unbounded stack implemented as a linked
   list of chunks. *)

(* This code raises several challenges:

   1- Do we somehow want recursive ownership by default (i.e., the
      parent stack owns the child stacks that it contains, and these
      children are pairwise disjoint)? Or do we want to explicitly
      express these properties? The former approach seems appealing
      but is tricky; the system must somehow check that ownership is
      never duplicated, and must recognize that [push] consumes the
      ownership of an element, while [pop] produces the ownership of
      an element.

   2- How do we express the invariants of the data structure, namely
      a- the view of the composite structure is the concatenation of
         the view of the front chunk and the views of the chunks held
         in the tail?
      b- every chunk in the tail is full.
      Depending on how we deal with ownership and logical views, the
      answer to this question may vary widely. If we have recursive
      ownership, then the logical view of the [tail] structure can be
      a sequence of sequences; otherwise, it might be a sequence of
      locations. *)

module StackOfStacks (P : STACK) (C : STACK) : STACK = struct

  (*@ predicate feasible (n : integer) =
        exists c p .
        n <= c + c * p && C.feasible(c) && P.feasible(p) *)

  type 'a stack = {
    (* A front chunk. *)
    mutable front : 'a C.stack;
    (* The tail: a stack of full chunks. *)
    tail : 'a C.stack P.stack;
  }
  (*@ mutable model view : 'a seq =
        C.view front ++ flatten (map C.view (P.view tail)) *)
  (*@ invariant feasible(length(view)) *)
  (*@ invariant forall chunk ∈ (P.view tail). maximal(length(C.view chunk)) *)
  (*@ invariant C.view front = empty -> P.view tail = empty *)

  let is_empty s =
    C.is_empty s.front

  let is_full s =
    C.is_full s.front && P.is_full s.tail

  let create () =
    let front = C.create () in
    let tail = P.create () in
    { front; tail }

  let push x s =
    assert (not (is_full s));
    if C.is_full s.front
    then begin
      P.push s.front s.tail;
      s.front <- C.create()
    end;
    assert (not (C.is_full s.front));
    C.push x s.front

  let pop s =
    assert (not (C.is_empty s.front));
    let x = C.pop s.front in
    if C.is_empty s.front && not (P.is_empty s.tail) then
      s.front <- P.pop s.tail;
    x

end

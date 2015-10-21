(* We re-use the dependent types of bounded integers as given in the course. *)

Require Import Arith List.
Set Implicit Arguments.

Definition bnat (n : nat) : Type := { m : nat | m < n }.

(* Q1. Implement the following function that inject (if possible)
   a nat into a bnat. If the nat is too big, you could return
   a bnat containing 0.
   Hint: use the boolean function leb on natural numbers and its
   companion theorems. *)

Definition mkbound : forall m, 0 < m -> nat -> bnat m.
Proof.
(* When you are finished, replace Admitted by Defined rather than Qed. *)
Admitted.

(* Q2, prove that if you have an element in bnat m, then 0 < m. *)

Lemma bound_non_0 :  forall m, bnat m -> 0 < m.

Admitted.

(* Q3, Define a function that increments a bounded natural number and returns
   a bounded natural number (with the same bound),  falling back on 0
   if the bound is reached.  This uses the answers of the previous two
   questions.
   incr_bound : forall m, bnat m -> bnat m
*)

(* Q4. Define a function that takes as input m, m', a proof that
   m < m', a bounded number smaller than m, and returns a
   number smaller than m'

   extend_bound : forall m m':nat, m < m' -> bnat m -> bnat m'
*)


(* Q5. Implement the following function.
   Feel free to try several approaches. *)

Definition is_prefix_of A (u v : list A) := exists w, u ++ w = v.

Definition firstn : forall A (l:list A) n, n <= length l ->
 { l' | n = length l' /\ is_prefix_of l' l }.
Proof.
Admitted.

(* Implementation of finite sets of integers.

   We would like to precisely implement the following interface
   for sets of integers
*)

Require Import ZArith.
Open Scope Z_scope.

Parameter set : Type.
Parameter In : Z -> set -> Prop.
Parameter mem : forall x s, { In x s }+{ ~ In x s }.
Parameter add : forall x s, { s' | forall y, In y s' <-> x=y \/ In y s }.

(* Q6. Propose an naive implementation with set := list Z *)


(* We propose the following way of stating that a list is sorted *)

Inductive sorted : list Z -> Prop :=
| sorted_0 : sorted nil
| sorted_1 : forall a, sorted (a::nil)
| sorted_2 : forall a b l, a <= b -> sorted (b::l) -> sorted (a::b::l).
Hint Constructors sorted.

(* The following properties might help. Proving then is not a priority here,
   but you can try later (at the end of the session). *)

Lemma sorted_inv : forall l a, sorted (a::l) -> sorted l.
Admitted.

Lemma sorted_cons : forall l x, sorted l -> (forall y, List.In y l -> x<=y) ->
 sorted (x::l).
Admitted.

Lemma in_above : forall l a x, sorted (a::l) -> List.In x l -> a<=x.
Admitted.

(* Q7. Implement more clever functions for set := { l : list Z | sorted l } *)

(* Q8. Try the Extraction command on the functions implemented
   during this session *)
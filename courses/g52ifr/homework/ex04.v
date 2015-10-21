(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 4 (Arithmetic)
    published 7/11/11, deadline 15/11/11, 18:00 electronic submission

    Use
    $ cw submit ex04.v
    on one of the CS servers
    then look for the coursework 425 labelled 'g52cfr coursework 4' 
    and enter the associated code.

    Multiple submissions are allowed, up to the deadline.

    Try to fill in the missing proofs, using only the basic tactics presented
    in the lectures.
    Do not use auto or tauto. Do not use any additional libraries.

**)

Section Ex04.

(** We are using all the results from the lecture. Please download the file Arith.v
    from the webpage and store it in the same directory. *)
Load Arith.

(** 1 **)

(* (5 points)
    Each proven theorem counts for 5/8 points. *)


Section Semiring.
(*
We have already shown (in the lecture) that nat with (+,0) is a commutative monoid.
Complete showing that nat with (+,0) and ( *,1) forms a commutative semiring by
proving the following theorems.*)

Theorem mult_1_l : forall n, 1 * n = n.
Theorem mult_1_r : forall n, n * 1 = n.
Theorem mult_assoc : forall n m p, n * (m * p) = n * m * p.
Theorem mult_comm : forall n m, n * m = m * n.
Theorem mult_0_l : forall n, 0 * n = 0.
Theorem mult_0_r : forall n, n * 0 = 0.
Theorem mult_plus_distr_l : forall n m p, n * (m + p) = n * m + n * p.
Theorem mult_plus_distr_r : forall n m p, (n + m) * p = n * p + m * p.

(*
Hints:
- you can use the results from Arith
- you may have to prove auxilliary results (lemmas)
- you may need to prove the theorems in a particular order 
  (you are allowed to reorder).
- the following tactics may be helpful:
  symmetry : turns an equation around.
  pattern t : focusses the next rewrite on a particular subterm t.
  pattern t at n : focusses rewrite on the nth occurence of a subterm t.

If you can't prove a particular theorem change "Theorem" to "Axiom".
This way you can use this proposition to prove others.
*)


(** 2 **)

Section asym.

(* Show that leq is antisymmetric. *)

(* (5 points)
   You get the points for completing the proof of le_asym using some lemmas you have proven.
   You may loose 1-2 points if the proof is extremely long and complicated, or if you use
   tactics inappropriately. You may earn points for reasonable but unfinished attempts. *)

Notation "m <= n" := (leq m n).

Theorem le_asym : forall (m n : nat), m <= n -> n <= m -> m=n.

(*
Hints: This will require proving some lemmas about addition.
       All the hints from the 1st part apply here as well.
*)

End asym.

End Ex04.
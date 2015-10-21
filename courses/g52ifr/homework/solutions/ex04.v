(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 4 (Arithmetic)
    published 7/11/11, deadline 15/11/11, 18:00 electronic submission

    Use
    $ cw submit ex04.v
    on one of the CS servers
    then look for the coursework ??? labelled 'g52cfr coursework 4' 
    and enter the associated code.

    Multiple submissions are allowed, up to the deadline.

    Try to fill in the missing proofs, using only the basic tactics presented
    in the lectures.
    Do not use auto or tauto. Do not use any additional libraries.

**)

Section Ex04.

(** We are using all the results from the lecture. *)
Load Arith.

(** 1 **)

Section Semiring.
(*
Complete showing that nat with + and * forms a semiring by proving the following therems.

Hints:
- you can use the results from Arith
- you may have to prove auxilliary results (lemmas)
- you may need to prove the theorems in a particular order 
  (you are allowed to reorder).
- the following tactics may be helpful:
  symmetry : turns an equation around.
  pattern t : focusses the next rewrite on a particular subterm.
  pattern t at n : focusses rewrite on the nth occurence of a subterm.
*)
Theorem mult_0_l : forall n, 0 * n = 0.
intro n.
reflexivity.
Qed.

Theorem mult_0_r : forall n, n * 0 = 0.
intro n.
induction n.
reflexivity.
simpl.
exact IHn.
Qed.

Theorem mult_1_l : forall n, 1 * n = n.
intro n.
simpl.
symmetry.
apply plus_n_O.
Qed.

Theorem mult_1_r : forall n, n * 1 = n.
intro n.
induction n.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Theorem mult_plus_distr_l : forall n m p, n * (m + p) = n * m + n * p.
intros n m p.
induction n.
reflexivity.
simpl.
rewrite IHn.
rewrite<- plus_assoc.
pattern (p + (n * m + n * p)).
rewrite plus_assoc.
pattern (p + n * m).
rewrite plus_comm.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite plus_assoc.
reflexivity.
Qed.


Theorem mult_plus_distr_r : forall n m p, (n + m) * p = n * p + m * p.
intros n m p.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
rewrite plus_assoc.
reflexivity.
Qed.


Theorem mult_assoc : forall n m p, n * (m * p) = n * m * p.
intros n m p.
induction n.
reflexivity.
simpl.
rewrite IHn.
rewrite mult_plus_distr_r.
reflexivity.
Qed.

Lemma mult_n_Sm : forall m n : nat, m * S n = m + m * n.
intros m n.
induction m.
reflexivity.
simpl.
rewrite IHm.
rewrite plus_assoc.
pattern (n + m).
rewrite plus_comm.
rewrite<- plus_assoc.
reflexivity.
Qed.

Theorem mult_comm : forall n m, n * m = m * n.
intros n m.
induction n.
simpl.
symmetry.
apply  mult_0_r.
simpl.
rewrite IHn.
rewrite mult_n_Sm.
reflexivity.
Qed.
End Semiring.

(** 2 **)

Section asym.

(* Show that leq is antisymmetric,
Hints: This may require proving some lemmas about addition.
       And all the hints form the 1st part apply.
*)

Lemma asym_lem : forall m k : nat, m = k + m -> k = 0.
intros m k.
induction m.
intro h1.
symmetry.
rewrite plus_n_O. 
exact h1.
intro sm.
apply IHm.
apply peano8.
rewrite sm.
rewrite<- plus_n_Sm.
reflexivity.
Qed.

Lemma zero_plus : forall k j : nat, k + j = 0 -> k = 0.
intros k j.
induction j.
intro h.
rewrite<- h.
apply plus_n_O.
intro h.
apply IHj.
assert (p : pred (k + S j) = 0).
rewrite h.
reflexivity.
rewrite<- p.
rewrite<- plus_n_Sm.
reflexivity.
Qed.


Notation "m <= n" := (leq m n).

Theorem le_asym : forall (m n : nat), m <= n -> n <= m -> m=n.
intros m n mn nm.
destruct mn as [k kmn].
destruct nm as [j jnm].
assert (H : m = (k + j) + m).
pattern m at 1.
rewrite kmn.
rewrite jnm.
rewrite plus_assoc.
reflexivity.
assert (kj0 : k + j = 0).
eapply asym_lem.
apply H.
assert (k0 : k = 0).
eapply zero_plus.
apply kj0.
rewrite k0 in kmn.
exact kmn.
Qed.

End asym.

End Ex04.
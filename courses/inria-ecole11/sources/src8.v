(* On inversion *)

Lemma le_n_0 : forall n:nat, n <= 0 -> n = 0.
Proof.
 intros n H; induction H.
(*

  n : nat
  ============================
   n = n

*)
reflexivity.

(*

1 subgoal
  
  n : nat
  m : nat
  H : n <= m
  IHle : n = m
  ============================
   n = S m
*)

Abort.

Lemma le_inv : forall n p: nat, n <= p ->
                                n = p \/ exists q:nat, p = S q /\ n <= q.
intros n p H.  destruct  H.
(*
2 subgoals
  
  n : nat
  ============================
   n = n \/ (exists q : nat, n = S q /\ n <= q)
*)
left;reflexivity.
(*
1 subgoal
  
  n : nat
  m : nat
  H : n <= m
  ============================
   n = S m \/ (exists q : nat, S m = S q /\ n <= q)

*)
 right; exists m;split;trivial.
Qed.

Lemma le_n_0_old_times : forall n:nat, n <= 0 -> n = 0.
Proof.
 intros n H.
 Check le_inv _ _ H.


 destruct (le_inv _ _ H) as [H0 | [q [Hq Hq0]]].
(*
2 subgoals
  
  n : nat
  H : n <= 0
  H0 : n = 0
  ============================
   n = 0

...
*)
assumption.
(*
1 subgoal
  
  n : nat
  H : n <= 0
 n : nat
  H : n <= 0
  q : nat
  Hq : 0 = S q
  Hq0 : n <= q
  ============================
   n = 0
*)
 discriminate Hq.
Qed.

Lemma le_Sn_Sp_inv: forall n p, S n <= S p -> n <= p.
Proof.
 intros n p H; inversion H.
 (*
2 subgoals
  
  n : nat
  p : nat
  H : S n <= S p
  H1 : n = p
  ============================
   p <= p
*)
constructor.


Require Import Le.
apply le_trans with (S n); repeat constructor; assumption.
Qed.

Definition Le (n p : nat) : Prop := exists q:nat, q + n = p.

Fixpoint LE (n p: nat): Prop :=
 match n, p with 0, _ => True
               | S _, 0 => False
               | S n', S p' => LE n' p'
 end.


Compute LE 7 34.

Compute LE 33 8.



(** Specifying programs with inductive predicates **)

Inductive Comparison : Type := Lt | Eq | Gt.

Inductive compare_spec (n p:nat) : Comparison -> Type :=
| lt_spec : forall Hlt : n < p, compare_spec n p Lt
| eq_spec :  forall Heq : n = p,  compare_spec  n p Eq
| gt_spec : forall Hgt : p < n, compare_spec n p Gt.


Goal compare_spec 5 6 Lt.
constructor.
auto with arith.
Qed.

Goal compare_spec 5 5 Eq.
constructor; reflexivity.
Qed.

Goal compare_spec 6 5 Gt.
constructor;auto with arith.
Qed.


Definition cmp_correct (cmp : nat -> nat -> Comparison)  :=
   forall n p, compare_spec n p (cmp n p).


Section On_compare_spec.
Variable cmp :  nat -> nat -> Comparison.
Hypothesis cmpP : cmp_correct cmp.

Section compare_spec_usage.
 Variable P : nat -> nat -> Comparison -> Prop.

 Goal forall n p , P n p (cmp n p).
 intros n p; destruct (cmpP n p).
 (*
 3 subgoals
  
  cmp : nat -> nat -> Comparison
  cmpP : cmp_correct cmp
  P : nat -> nat -> Comparison -> Prop
  n : nat
  p : nat
  Hlt : n < p
  ============================
   P n p Lt

subgoal 2 is:
  
  ...
  Heq : n = p
  ============================
   P n p Eq

subgoal 3 is:
  
  ...
  Hgt : p < n
  ============================
   P n p Gt
*)
Abort.

End compare_spec_usage.
Require Import Omega.

Definition compare_rev (c:Comparison) :=
 match c with 
 | Lt => Gt
 | Eq => Eq
 | Gt => Lt
 end.

Lemma cmp_rev : forall n p, cmp n p = compare_rev (cmp p n).
Proof.
 intros n p. 
 destruct (cmpP n p);destruct (cmpP p n) ;trivial;try discriminate;
 intros; elimtype False; omega.
Qed.

Lemma cmp_antiym : forall n p, cmp n p = cmp p n -> n = p.
Proof.
 intros n p;rewrite cmp_rev; destruct (cmpP p n);auto ;try discriminate.
Qed.

Definition maxn n p := match cmp  n p with Lt => p | _ => n end.

Definition minn  n p := match cmp n p with Lt => n | _ => p end.


Lemma le_maxn: forall n p, n <= maxn n p.
Proof.
intros n p; unfold maxn.  
destruct (cmpP n p). 
(*
3 subgoals
  
  cmp : nat -> nat -> Comparison
  cmpP : cmp_correct cmp
  P : nat -> nat -> Comparison -> Prop
  n : nat
  p : nat
  Hlt : n < p
  ============================
   n <= p

subgoal 2 is:
 n <= n
subgoal 3 is:
 n <= n
*)

auto with arith.
auto with arith.
auto with arith.
Qed.



Lemma maxn_comm :  forall n p, maxn n p = maxn p n.
Proof.
intros n p; unfold maxn.   destruct (cmpP n p), (cmpP p n);omega.
Qed.

Lemma maxn_le: forall n p q, n <= q -> p <= q -> maxn n p <= q.
intros n p. unfold maxn.  destruct (cmpP n p); auto with arith.
Qed.

Lemma min_plus_maxn : forall n p, minn n p + maxn n p = n +p.
intros n p. unfold maxn, minn.  destruct (cmpP n p); auto with arith.
Qed.

End On_compare_spec.



Fixpoint compare (n m:nat) : Comparison := 
 match n, m with | 0,0 => Eq
                 | 0, S _ => Lt
                 | S _, 0 => Gt
                 | S p, S q => compare p q
 end.



Lemma compareP : cmp_correct compare.
red;induction n;destruct p;simpl;auto; try (constructor;auto with arith).
destruct (IHn p);constructor;auto with arith.
Qed.

Check maxn_comm _ compareP.





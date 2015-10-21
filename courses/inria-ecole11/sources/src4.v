Require Import Arith.
Require Import List.

(*** First examples ***)

Parameters (e f g : nat -> nat). 
Parameters (P Q R : nat -> nat -> Prop).

Axiom Pf : forall x, P x (f x).

Axiom Qg : forall y, Q y (g y).

Axiom PQR : forall x y z, P x y -> Q y z -> R x z.

Definition h (x:nat) := g (f x).

Axiom he : h = e.


Lemma exfgh x : R x (h x).
Proof.
apply (PQR _ (f x)).
  now apply Pf.
  unfold h.
now apply Qg.
Qed.

Lemma exfge x : R x (e x).
Proof.
apply (PQR _ (f x)).
  now apply Pf.
replace e with h.
  now apply Qg.
apply he.
Qed.

Parameter (A : nat -> Prop).

Axiom Aplus : forall n m : nat, A n -> A m -> A (n + m).

Lemma A5 : A 2 -> A 3 -> A 5.
Proof.
change 5 with (2 + 3).
now apply Aplus.
Qed.

(***  Natural Numbers ***)

Definition pred (x : nat) := match x with 0 => x | S p => p end.

Lemma S_pred x : x <> 0 -> S (pred x) = x.
Proof.
unfold pred.
  case x.
  intros Habs.
  now case Habs.
reflexivity.
Qed.

(* Companion theorems *)
SearchPattern (nat -> nat -> bool).
SearchAbout beq_nat.

Check beq_nat_true.

Definition pre2 (x : nat) := if beq_nat x 0 then 1 else pred x.

Lemma pre2pred n : n <> 0 -> pre2 n = pred n.
Proof.
case_eq (beq_nat n 0).
  intros Htrue.
  assert (Hx := beq_nat_true _ _ Htrue).
  rewrite Hx.
  intros Habs.
  now case Habs.
unfold pre2.
intro Hfalse.
rewrite Hfalse.
reflexivity.
Qed.

(***  Recursive functions ***)

Fixpoint add n m :=
    match n with 0 => m | S p => add p (S m) end.

Lemma addnS : forall n m, add n (S m) = S (add n m).
Proof.
intros n.
induction n as [|m ihm].
  reflexivity.
intros k.
simpl.
rewrite ihm.
reflexivity.
Qed.

(* what happens if we start with intros n m. induction n? *)

(* A similar example *)
Fixpoint sum (n : nat) :=
  match n with
    |0 => n
    |S m => S m + (sum m)
  end.

Lemma gauss_trick : forall n, 2 * (sum n) = n * (n + 1).
Proof.
intros n.
induction n.
  reflexivity.
simpl.
ring_simplify.
rewrite IHn.
ring.
Qed.

(* A companion theorem for the sum function *)
Lemma sum_step : forall n, sum (S n) = S n + (sum n).
Proof.
intros n.
case n.
  now trivial.
now trivial.
Qed.

(*** Examples on lists ***)

Print rev.

Fixpoint rev_app (A : Type)(l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | a :: tl => rev_app A tl (a :: l2)
  end.

Implicit Arguments rev_app.

Lemma rev_app_nil : forall A (l1 : list A), rev_app l1 nil = rev l1.
Proof.
intros A l1.
cut (forall l2, rev_app l1 l2 = rev l1 ++ l2).
  intros aux.
  rewrite aux.
  SearchPattern (_ ++ nil = _).
  rewrite app_nil_r.
  reflexivity.
induction l1 as [|t1 l1 ihl1].
  reflexivity.
intros l2.
simpl.
rewrite ihl1.
SearchPattern ((_ ++ _) ++ _ = _).
rewrite app_assoc_reverse.
simpl.
reflexivity.
Qed.
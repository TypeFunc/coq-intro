Require Import Omega.

Lemma size_induction (X : Type) (f : X -> nat) (p : X -> Prop) :
  (forall (x : X), (forall (y : X), f y < f x -> p y) -> p x) -> (forall (x : X), p x).
Proof.
  intros A x.
  (** What we are trying to prove shows up as the antecedent of A, so we apply A... *)
  apply A.
  (** ...and the goal becomes proving the antecedent of A. *)
  assert (G: forall n y, f y < n -> p y).
  { intro n. induction n as [ | n'].
    - intros y B. exfalso. omega.
    - intros y B. apply A. intros z C. apply IHn'. omega.
  }
  apply G.
Qed.

Print size_induction.
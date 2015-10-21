(** Addition on the natural numbers is commutative. *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat
.

Fixpoint plus (x y : nat) : nat :=
match x with
  | O => y
  | S x' => S (plus x' y)
end.

Notation "x + y" := (plus x y) (at level 50, left associativity). 

Lemma plus_O (x : nat) : x + O = x.
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma plus_S (x y : nat) : x + (S y) = S (x + y).
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma plus_comm (x y : nat) : x + y = y + x.
Proof.
  induction x.
  - simpl. rewrite plus_O. reflexivity.
  - simpl. rewrite IHx. rewrite plus_S. reflexivity.
Qed.
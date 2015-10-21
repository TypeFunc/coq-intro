Set Implicit Arguments.
Unset Strict Implicit.
Require Import Omega.
Require Import List.
Import ListNotations.

Definition surjective (X Y : Type) (f : X -> Y) : Prop := 
  forall y, exists x, f x = y.

Theorem Cantor (X : Type) : not (exists f : X -> X -> Prop, surjective f).
Proof.
  intros [f A].
  pose (g := fun x => not (f x x)).
  destruct (A g) as [x B].
  assert (C : g x <-> f x x).
  {
    rewrite B. tauto.
  }
  unfold g in C. tauto.
Qed.  

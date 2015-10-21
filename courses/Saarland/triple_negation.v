(** First try (proof script) *)
Goal forall X : Prop, not (not (not X)) -> not X.
Proof.
  intros X A.
  (*** Claim not X is X -> False *)
  intro B.
  (*** A : not not not X is the same as not not X -> False *)
  apply A.
  (*** Claim not not X is not X -> False *)
  intro C.
  (*** C : not X is the same as X -> False *)
  apply C.
  exact B.
Qed.
Print Unnamed_thm.

(** Returns:
fun (X : Prop) (A : ~ ~ ~ X) (B : X) => A (fun C : ~ X => C B)
     : forall X : Prop, ~ ~ ~ X -> ~ X
*)

(** Second try (towards a proof term) *)
Goal forall X : Prop, not (not (not X)) -> not X.
Proof.
  intros X A.
  (*** Claim not X is X -> False *)
  intro B.
  (*** A : not not not X is the same as not not X -> False *)
  apply A.
  (*** Claim not not X is not X -> False *)
  intro C.
  (*** C : not X is the same as X -> False *)
  exact (C B).
Qed.

(** We are trying to build the following proof term from the bottom up:
fun (X : Prop) (A : ~ ~ ~ X) (B : X) => A (fun C : ~ X => C B)
*)

(** Third try (closer to a proof term) *)
Goal forall X : Prop, not (not (not X)) -> not X.
Proof.
  intros X A.
  (*** Claim not X is X -> False *)
  intro B.
  (*** A : not not not X is the same as not not X -> False *)
  apply A.
  (*** ...and not not X is the same as not X -> False *)
  (*** intro corresponds to a lambda abstraction *)
  exact (fun C => C B).
Qed.

(** Fourth try (even closer to a proof term) *)
Goal forall X : Prop, not (not (not X)) -> not X.
Proof.
  intros X A.
  (*** not X is X -> False *)
  intro B.
  (*** A : not not not X is not not X -> False *)
  exact (A (fun C => C B)).
Qed.

(** We are trying to build the following proof term from the bottom up:
fun (X : Prop) (A : ~ ~ ~ X) (B : X) => A (fun C : ~ X => C B)
*)

(** Fifth try (proof term) *)
Goal forall X : Prop, not (not (not X)) -> not X.
Proof.
  exact (fun X A B => A (fun C => C B)).
Qed.

Print Unnamed_thm3.
(** first try (proof script) *)
Goal forall X Y : Prop, (forall Z : Prop, (X -> Y -> Z) -> Z) -> X.
Proof.
  intros X Y A.
  apply A.
  intros B C.
  exact B.
Qed.

Print Unnamed_thm.

(** second try (exact proof) *)
Goal forall X Y : Prop, (forall Z : Prop, (X -> Y -> Z) -> Z) -> X.
Proof.
  exact (fun (X Y : Prop) (A : forall Z : Prop, (X -> Y -> Z) -> Z) =>
           A X (fun (B : X) (C : Y) => B)).
Qed.

(** third try (exact proof with implicit types) *)
Goal forall X Y : Prop, (forall Z : Prop, (X -> Y -> Z) -> Z) -> X.
Proof.
  exact (fun X Y A => A X (fun B C => B)).
Qed.
(** Examples of proof terms. *)

(** --- EXAMPLE 1 --- *)
(** First try *)
Goal forall X Y : Prop, X -> Y -> X.
Proof.
  intros X Y A B. exact A.
Qed.

(** Second try (with exact proof term) *)
Goal forall X Y : Prop, X -> Y -> X.
Proof.
  intros X Y. exact (fun A : X => fun B : Y => A).
Qed.

(** Third try (with exact proof term with implicit types) *)
Goal forall X Y : Prop, X -> Y -> X.
Proof.
  exact (fun X Y A B => A).
Qed.

(** Fourth try (with exact proof term with explicit types) *)
Goal forall X Y : Prop, X -> Y -> X.
Proof.
  exact (fun X : Prop => fun Y : Prop => fun A : X => fun B : Y => A).
Qed.

(** --- EXAMPLE 2 --- *)
(** First try (exact proof term) *)
Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  (** A : X -> Y,  B : Y -> Z,  C : X *)
  exact (fun X Y Z A B C => B (A C)).
Qed.

(** Second try (with a proof script) *)
Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  intros X Y Z A B C.
  apply B.
  apply A.
  exact C.
Qed.


(** Third try (minor mods of Second try). *)
Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  intros X Y Z A B C.
  apply B, A, C.  (* You can apply multiple things with a comma. *)
                  (* Here `apply C` has same effect as `exact C`. *)
Qed.


(** After writing a proof script with Coq, we can look at the 
    proof term we created with the `Show Proof` command. *)
Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  intros X Y Z A B C.
  apply B, A, C. Show Proof.
Qed. 

(** We can also put `Show Proof` in the middle of a proof to 
    show a partial proof with holes. *)
Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  intros X Y Z A B C. 
  Show Proof.
  apply B.
  Show Proof.
  apply A.
  Show Proof.
  apply C.
Qed.


(** --- EXAMPLE 2 --- *)
(** First try (exact proof term with explicit types) *)
Goal forall X Y Z : Prop, (X -> Y -> Z) -> (X -> Y) -> X -> Z.
Proof.
  exact (fun (X Y Z : Prop) (A: X -> Y -> Z) (B: X -> Y) (C: X) => A C (B C)).
Qed.

(** Second try (exact proof term with implicit types) *)
Goal forall X Y Z : Prop, (X -> Y -> Z) -> (X -> Y) -> X -> Z.
Proof.
  exact (fun X Y Z A B C => A C (B C)).
Qed.

(** Third try (proof sequence) *)
Goal forall X Y Z : Prop, (X -> Y -> Z) -> (X -> Y) -> X -> Z.
Proof.
  intros X Y Z A B C.
  apply A.
  - exact C.
  - exact (B C).  (* or - apply B, C. *)
  Show Proof.  (* the proof term is the same as in our first try *)
Qed.

Print Unnamed_thm10.  
(* This shows the proof term, and shows type "type" of the proof term
   is the proposition that it proves.  This is the Curry-Howard correspondence!
   A proposition P is a type and a proof of P is a term of type P. *)
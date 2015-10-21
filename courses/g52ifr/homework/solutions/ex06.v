(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 6 (Expressions and Coq in Coq)
    published 21/11/11, deadline 29/11/11, 18:00 electronic submission

    Use
    $ cw submit ex06.v
    on one of the CS servers
    then look for the coursework ??? labelled 'g52cfr coursework 6' 
    and enter the associated code.

    Multiple submissions are allowed, up to the deadline.

    Try to fill in the missing proofs, using only the basic tactics presented
    in the lectures.
    Do not use any additional libraries.

**)

Section Ex06.

(** 1 (5 points) **)

Section BoolExpr.
Require Bool.
Open Scope bool_scope.

(* We define a type of boolean expressions with one variable. *)

Inductive Expr : Set :=
  | var : Expr
  | not : Expr -> Expr
  | and : Expr -> Expr -> Expr
  | or : Expr -> Expr -> Expr.

(* It's interpretation is a function on bool. *)

Fixpoint eval (e : Expr)(x : bool) : bool :=
  match e with
  | var => x
  | not e => negb (eval e x)
  | and e1 e2 => (eval e1 x) && (eval e2 x)
  | or e1 e2 => (eval e1 x) || (eval e2 x)
  end.

(* Define an operation on expressions which composes two expressions. *)

Fixpoint compose (e1 e2 : Expr) : Expr :=
  match e1 with
  | var => e2
  | not e1' => not (compose e1' e2)
  | and e11 e12 => and (compose e11 e2) (compose e12 e2) 
  | or e11 e12 => or (compose e11 e2) (compose e12 e2) 
  end.

(* and prove that it is correct. *)

Theorem composeThm : forall (e1 e2 : Expr)(b : bool),
  eval (compose e1 e2) b = eval e1 (eval e2 b).
intros e1 e2 b.
induction e1.
reflexivity.
simpl.
rewrite IHe1.
reflexivity.
simpl.
rewrite IHe1_1.
rewrite IHe1_2.
reflexivity.
simpl.
rewrite IHe1_1.
rewrite IHe1_2.
reflexivity.
Qed.

(* We define a predicate which expresses that an expression doesn't
   contain any or.
*)

Fixpoint NoOr (e : Expr) : Prop :=
  match e with
  | var => True
  | not e => NoOr e
  | and e1 e2 => NoOr e1 /\ NoOr e2
  | or e1 e2 => False
  end.

(* Define a function which eliminate ors. How? *)

Fixpoint elimOr (e : Expr) : Expr :=
  match e with 
  | var => var
  | not e => not (elimOr e)
  | and e1 e2 => and (elimOr e1) (elimOr e2)
  | or e1 e2 => not (and (not (elimOr e1)) (not (elimOr e2)))
  end.

Lemma dmbool : forall (b c : bool), b || c = negb ((negb b) && (negb c)).
destruct b.
reflexivity.
destruct c; reflexivity.
Qed.

(* and show that it preserves the meaning. *)

Lemma elimOrSound : forall (e : Expr)(b: bool), eval e b = eval (elimOr e) b.
intros e b.
induction e.
reflexivity.
simpl. rewrite IHe. reflexivity.
simpl. rewrite IHe1. rewrite IHe2. reflexivity.
simpl. rewrite IHe1. rewrite IHe2. apply dmbool.
Qed.

(* And that the result indeed doesn't contain any or. *)

Lemma elimOrNoOr : forall (e : Expr), NoOr (elimOr e).
intro e.
induction e.
split. exact IHe.
split. exact IHe1. exact IHe2.
simpl. split. exact IHe1. exact IHe2.
Qed.

End BoolExpr.

(** 2 (5 points) **)

Section MetaConj.

(* We extend the logic we have considered in the lecture
   by conjunction and extend the results.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Inductive Formula : Set :=
  | Var : string -> Formula
  | Impl : Formula -> Formula -> Formula
  | And : Formula -> Formula -> Formula.

Notation "x ==> y"  := (Impl x y) (at level 30, right associativity).
Notation "x //\\ y" := (And x y) (at level 20, left associativity).

Definition Hyps : Set := list Formula.

Inductive ND_Proof : Hyps -> Formula -> Prop :=
| nd_ass : forall (Hs : Hyps)(P : Formula),
             ND_Proof (P :: Hs) P
| nd_weak : forall (Hs : Hyps)(P Q : Formula),
             ND_Proof Hs P -> ND_Proof (Q :: Hs) P
| nd_intro : forall (Hs : Hyps)(P Q : Formula),
             ND_Proof (P :: Hs) Q -> ND_Proof Hs (P ==> Q)
| nd_apply : forall (Hs : Hyps)(P Q : Formula),
             ND_Proof Hs (P ==> Q) -> ND_Proof Hs P -> ND_Proof Hs Q
(* The nd_split rule corresponds exactly to the split tactic. *)
| nd_split : forall (Hs : Hyps)(P Q : Formula),
             ND_Proof Hs P -> ND_Proof Hs Q -> ND_Proof Hs (P //\\ Q)
(* Our version of destruct is slightly different than the one 
   implemented in Coq. Can you see the difference? *)
| nd_destruct : forall (Hs : Hyps)(P Q R : Formula),
             ND_Proof (P :: Q :: Hs) R 
             -> ND_Proof Hs (P //\\ Q)
             -> ND_Proof Hs R.

(* Prove swap using the rules above. *)
Lemma nd_swap : 
  forall (Hs : Hyps)(P Q : Formula), 
          ND_Proof Hs (P //\\ Q ==> Q //\\ P).
intros Hs P Q.
apply nd_intro.
eapply nd_destruct.
apply nd_split.
apply nd_weak. apply nd_ass.
apply nd_ass.
apply nd_ass.
Qed.

(* We are defining a number of new combinators: *)

Definition FST (P Q : Formula) : Formula :=
  (P //\\ Q ==> P).
Definition SND (P Q : Formula) : Formula :=
  (P //\\ Q ==> Q).
Definition PAIR (P Q : Formula) : Formula :=
  (P ==> Q ==> P //\\ Q).

(* Prove them using the rules above. *)

Lemma nd_FST : forall (Hs : Hyps)(P Q : Formula), 
          ND_Proof Hs (FST P Q).
intros Hs P Q.
unfold FST.
apply nd_intro.
eapply nd_destruct.
apply nd_ass.
apply nd_ass.
Qed.

Lemma nd_SND : forall (Hs : Hyps)(P Q : Formula), 
          ND_Proof Hs (SND P Q).
intros Hs P Q.
unfold SND.
apply nd_intro.
eapply nd_destruct.
apply nd_weak. apply nd_ass.
apply nd_ass.
Qed.

Lemma nd_PAIR : forall (Hs : Hyps)(P Q : Formula), 
          ND_Proof Hs (PAIR P Q).
intros Hs P Q.
unfold PAIR.
apply nd_intro.
apply nd_intro.
apply nd_split.
apply nd_weak. apply nd_ass.
apply nd_ass.
Qed.

(* We extend combinatory logic by adding the above combinators as
   additional axioms. *)

Definition K (P Q : Formula) : Formula := P ==> Q ==> P.
Definition S (P Q R : Formula) : Formula := 
  (P ==> Q ==> R) ==> (P ==> Q) ==> P ==> R.

Inductive CL_Proof : Hyps -> Formula -> Prop :=
| cl_ass : forall (Hs : Hyps)(P : Formula),
             CL_Proof (P :: Hs) P
| cl_weak : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof Hs P -> CL_Proof (Q :: Hs) P
| cl_K : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof Hs (K P Q)
| cl_S : forall (Hs : Hyps)(P Q R: Formula),
             CL_Proof Hs (S P Q R)
| cl_FST : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof Hs (FST P Q)
| cl_SND : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof Hs (SND P Q)
| cl_PAIR : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof Hs (PAIR P Q)
| cl_apply : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof Hs (P ==> Q) -> CL_Proof Hs P -> CL_Proof Hs Q.

(* Show that provability in combinatory logic implies provability
   in natural deduction.
   Hints: Extend the corresponding theorem in Meta.v by 
         the new cases.
         You are welcome to copy and paste proofs from Meta.v
         where appropriate.
*)

Lemma nd_K : 
forall (Hs : Hyps)(P Q : Formula), 
          ND_Proof Hs (K P Q).
intros Hs P Q.
unfold K.
apply nd_intro.
apply nd_intro.
apply nd_weak.
apply nd_ass.
Qed.


Lemma nd_S : forall (Hs : Hyps)(P Q R : Formula), 
                   ND_Proof Hs (S P Q R).
intros Hs P Q R.
unfold S.
apply nd_intro.
apply nd_intro.
apply nd_intro.
eapply nd_apply. eapply nd_apply.
apply nd_weak. apply nd_weak. apply nd_ass.
apply nd_ass. 
eapply nd_apply.
apply nd_weak. apply nd_ass.
apply nd_ass.
Qed.


Lemma cl2nd : 
forall (Hs : Hyps)(P : Formula), 
  CL_Proof Hs P -> ND_Proof Hs P.
intros Hs P H.
dependent induction H.
apply nd_ass.
apply nd_weak.
exact IHCL_Proof.
apply nd_K.
apply nd_S.
apply nd_FST.
apply nd_SND.
apply nd_PAIR.
eapply nd_apply.
apply IHCL_Proof1.
apply IHCL_Proof2.
Qed.

Definition I (P : Formula) : Formula := P ==> P.

Lemma cl_I : 
forall (Hs : Hyps)(P : Formula), 
         CL_Proof Hs (I P).
intros Hs P.
unfold I.
eapply cl_apply.
eapply cl_apply.
apply cl_S.
apply cl_K.
instantiate (1:= P ==> P ).
apply cl_K.
Qed.

(* Prove that combinatory logic is closed under the intro rule.
   Hint: Extend the corresponding lemma in Meta.v *)

Lemma cl_intro : 
forall (Hs : Hyps)(P Q : Formula),
    CL_Proof (P :: Hs) Q 
 -> CL_Proof Hs (P ==> Q).
intros Hs P Q H.
dependent induction H.
apply cl_I.
eapply cl_apply.
apply cl_K.
exact H.
eapply cl_apply.
apply cl_K.
apply cl_K.
eapply cl_apply.
apply cl_K.
apply cl_S.
eapply cl_apply.
apply cl_K.
apply cl_FST.
eapply cl_apply.
apply cl_K.
apply cl_SND.
eapply cl_apply.
apply cl_K.
apply cl_PAIR.
eapply cl_apply.
eapply cl_apply.
apply cl_S.
apply IHCL_Proof1.
reflexivity.
apply IHCL_Proof2.
reflexivity.
Qed.

(* Derive the following principle in combinatory logic *)

Lemma cl_elim : forall (Hs : Hyps)(P Q R : Formula), 
  CL_Proof Hs ((Q ==> P ==> R) ==> (P //\\ Q ==> R)).
intros Hs P Q R.
apply cl_intro.
apply cl_intro.
eapply cl_apply.
eapply cl_apply.
apply cl_weak. apply cl_ass.
eapply cl_apply.
apply cl_SND.
apply cl_ass.
eapply cl_apply.
apply cl_FST.
apply cl_ass.
Qed.

(* Show that provability in natural deduction implies provability
   in combinatory logic.
   Hint: Extend the corresponding theorem in Meta.v
*)

Lemma nd2cl : forall (Hs : Hyps)(P : Formula), 
 ND_Proof Hs P -> CL_Proof Hs P.
intros Hs P H.
dependent induction H.
apply cl_ass.
apply cl_weak. exact IHND_Proof.
apply cl_intro. exact IHND_Proof.
eapply cl_apply.
apply IHND_Proof1.
exact IHND_Proof2.
eapply cl_apply.
eapply cl_apply.
apply cl_PAIR.
exact IHND_Proof1.
exact IHND_Proof2.
eapply cl_apply.
eapply cl_apply.
apply cl_elim.
eapply cl_intro.
eapply cl_intro.
apply IHND_Proof1.
exact IHND_Proof2.
Qed.


End MetaConj.

End Ex06.
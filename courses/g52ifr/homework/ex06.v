(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 6 (Expressions and Coq in Coq)
    published 21/11/11, deadline 29/11/11, 18:00 electronic submission

    Use
    $ cw submit ex06.v
    on one of the CS servers
    then look for the coursework 437 labelled 'g52cfr coursework 6' 
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
(* insert solution *)

(* and prove that it is correct. *)

Theorem composeThm : forall (e1 e2 : Expr)(b : bool),
  eval (compose e1 e2) b = eval e1 (eval e2 b).

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

(* and show that it preserves the meaning. *)

Lemma elimOrSound : forall (e : Expr)(b: bool), eval e b = eval (elimOr e) b.

(* And that the result indeed doesn't contain any or. *)

Lemma elimOrNoOr : forall (e : Expr), NoOr (elimOr e).

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

Lemma nd_SND : forall (Hs : Hyps)(P Q : Formula), 
          ND_Proof Hs (SND P Q).

Lemma nd_PAIR : forall (Hs : Hyps)(P Q : Formula), 
          ND_Proof Hs (PAIR P Q).


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


Lemma cl2nd : 
forall (Hs : Hyps)(P : Formula), 
  CL_Proof Hs P -> ND_Proof Hs P.


(* Prove that combinatory logic is closed under the intro rule.
   Hint: Extend the corresponding lemma in Meta.v *)

Lemma cl_intro : 
forall (Hs : Hyps)(P Q : Formula),
    CL_Proof (P :: Hs) Q 
 -> CL_Proof Hs (P ==> Q).

(* Derive the following principle in combinatory logic *)

Lemma cl_elim : forall (Hs : Hyps)(P Q R : Formula), 
  CL_Proof Hs ((Q ==> P ==> R) ==> (P //\\ Q ==> R)).

(* Show that provability in natural deduction implies provability
   in combinatory logic.
   Hint: Extend the corresponding theorem in Meta.v
*)

Lemma nd2cl : forall (Hs : Hyps)(P : Formula), 
 ND_Proof Hs P -> CL_Proof Hs P.

End MetaConj.

End Ex06.
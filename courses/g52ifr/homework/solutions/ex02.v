(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 2 (Predicate logic)
    published 17/10/11, deadline 25/10/11, 18:00 electronic submission

    Use
    $ cw submit ex02.v
    on one of the CS servers
    then look for the coursework ??? labelled 'g52cfr coursework 1' 
    and enter the associated code.

    Multiple submissions are allowed, up to the deadline.

    Try to fill in the missing proofs, using only the basic tactics presented
    in the first lectures (i.e. exact, intro(s), apply, destruct, left, right, split).
    Do not use auto or tauto. Do not use any libraries.

    Note that not all the propositions below are provable!
    Comment out the ones, which you think are not provable and 
    mark them with the words "not provable", if you are sure.

**)

Section Relations.

Variable People : Set.

Variables Male Female : People -> Prop.
(* Male x = x is a male
   Female x = x is a female
*)

Variable Parent : People -> People -> Prop.
(* Parent x y = x is the parent of y *)

Variable Married : People -> People -> Prop.
(* Married x y = x is married to y *)

(** Define the following relations:
   - Father
   - Mother
   - Brother
   - Sister
   - Halfbrother
   - Halfsister
   - MotherInLaw
   - FatherInLaw
   - Aunt
   - Uncle
you are encourange to use auxilliary definitions to 
avoud having to repeat definitions. 

As an example we define Father:
*)
Definition Father (x y : People) :=
  Male x /\ Parent x y.

Definition Mother (x y : People) :=
  Female x /\ Parent x y.

Definition Sibling (x y : People) :=
  ~ (x = y) /\ forall z : People, Parent z x <-> Parent z y.

Definition Sister (x y : People) :=
  Female x /\ Sibling x y.

Definition Brother (x y : People) :=
  Male x /\ Sibling x y.

Definition HalfSibling (x y : People) := 
  ~ (x = y) /\ exists z : People, Parent z x /\ Parent z y
  /\ exists z:People, ~ (Parent z x /\ Parent z y).

Definition Halfsister (x y : People) :=
  Female x /\ HalfSibling x y.

Definition Halfbrother (x y : People) :=
  Male x /\ Sibling x y.

Definition Grandparent (x y : People) := 
  exists z:People, Parent x z /\ Parent z y.

Definition Grandfather (x y : People) :=
  Male x /\ Grandparent x y.

Definition Grandmother (x y : People) :=
  Female x /\ Grandparent x y.

Definition ParentInLaw (x y : People) :=
  exists z:People, Parent x z /\ Married z y.

Definition MotherInLaw (x y : People) :=
  Female x /\ ParentInLaw x y.

Definition FatherInLaw (x y : People) :=
  Male x /\ ParentInLaw x y.

Definition SiblingInLaw (x y : People) :=
  exists x':People, Married x x' /\ Sibling x' y.

Definition BrotherInLaw (x y : People) :=
  Male x /\ SiblingInLaw x y.

Definition SisterInLaw (x y : People) :=
  Female x /\ SiblingInLaw x y.

Definition AuntOrUncle (x y : People) :=
  exists z:People, (Sibling x z \/ SiblingInLaw x z) /\ Parent z y.

Definition Aunt (x y : People) :=
  Female x /\ AuntOrUncle x y.

Definition Uncle (x y : People) :=
  Male x /\ AuntOrUncle x y.

End Relations.

Section Tautologies.

Variable A B  : Set.

Variable P : A -> Prop.
Variables R : A -> B -> Prop.

Require Import Coq.Logic.Classical.
(* Try to prove the following propositions.
   If you can't prove a propsoition comment is out.
   If you are sure that a proposition is not provable in general
   then add the words *unprovable* in the comment.

   You can use classical logic, if you need to.
   If you use classical logic uxsnneccessarily you will loose 
   poins.
*)

(*
Lemma forallexcom : (forall x:A, exists y : B, R x y)
                  -> exists y : B, forall x : A, R x y.
unprovable *)

Lemma exforallcom : (exists x : A,forall y : B, R x y)
                  -> forall y : B, exists x : A, R x y.
intros H y.
destruct H as [a r].
exists a.
apply r.
Qed.

Lemma demorgan1 : (~ exists x : A, P x) <-> forall x:A , ~ P x.
split.
intros H x p.
apply H.
exists x.
exact p.
intros H1 H2.
destruct H2 as [x p].
assert (H1x : ~ P x).
apply H1.
apply H1x.
exact p.
Qed.


Lemma demorgan2 : (~ forall x : A, P x) <-> exists x : A, ~ P x.
split.
intro H.
apply NNPP.
intro ne.
apply H.
intro x.
apply NNPP.
intro np.
apply ne.
exists x.
exact np.
intros H1 H2.
destruct H1 as [a np].
apply np.
apply H2.
Qed.

Lemma dp : (exists x:A, True) -> exists x:A, P x -> forall x:A, P x.
intros ne.
destruct (classic (forall x:A,P x)) as [alld | nalld].
destruct ne as [x _].
exists x.
intros px y.
apply alld.
assert (H : exists x:A, ~P x).
apply NNPP.
intro nne.
apply nalld.
intro a.
apply NNPP.
intro np.
apply nne.
exists a.
exact np.
destruct H as [tt nd].
exists tt.
intros ptt x.
assert (ic : False).
apply nd.
apply ptt.
destruct ic.
Qed.

Lemma transsym : forall x y z : A, x = y -> x = z -> y = z.
intros x y z xy xz.
rewrite<- xy.
exact xz.
Qed.

Lemma eqneq : forall x y z : A, x = y -> ~ (x = z) -> ~ (y = z).
intros x y z xy nxz yz.
apply nxz.
rewrite xy.
exact yz.
Qed.

Lemma symneq : forall x y : A, ~(x = y) -> ~(y = x).
intros x y nxy yx.
apply nxy.
rewrite yx.
reflexivity.

(*
Lemma transneq : forall x y z : A, ~(x = y) -> ~(y = z) -> ~(x = z).
unprovable.
*)




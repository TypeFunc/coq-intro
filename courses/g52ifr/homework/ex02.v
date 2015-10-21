(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 2 (Predicate logic)
    published 17/10/11, deadline 1/11/11, 18:00 electronic submission (extended)

    Use
    $ cw submit ex02.v
    on one of the CS servers
    then look for the coursework 413 labelled 'g52cfr coursework 2' 
    and enter the associated code.

    Multiple submissions are allowed, up to the deadline.

    Try to fill in the missing proofs, using only the basic tactics presented
    in the first lectures (i.e. exact, intro(s), apply, destruct, left, right, split,
    exists).
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

If you are unsure what these terms mean, check them out
on wiktionary (http://en.wiktionary.org/wiki/).
In some cases there is a choice, document which
alternative you have been using.

As an example we define Father:
*)
Definition Father (x y : People) :=
  Male x /\ Parent x y.


Section Tautologies.

Variable A B  : Set.

Variable P : A -> Prop.
Variables R : A -> B -> Prop.

Require Import Coq.Logic.Classical.
(* Try to prove the following propositions.
   If you can't prove a proposition comment is out.

    Use only the basic tactics presented in the lectures 
    (i.e. exact, intro(s), apply, destruct, left, right, split,
    exists). Don't use any automatc tactics or import
    any additional libraries.

   If you are sure that a proposition is not provable in general
   then add the words *unprovable* in the comment.

   You can use classical logic, if you need to.
   If you use classical logic unneccessarily you will loose 
   points.
*)

Lemma forallexcom : (forall x:A, exists y : B, R x y)
                  -> exists y : B, forall x : A, R x y.

Lemma exforallcom : (exists x : A,forall y : B, R x y)
                  -> forall y : B, exists x : A, R x y.

Lemma demorgan1 : (~ exists x : A, P x) <-> forall x:A , ~ P x.

Lemma demorgan2 : (~ forall x : A, P x) <-> exists x : A, ~ P x.

Lemma dp : (exists x:A, True) -> exists x:A, P x -> forall x:A, P x.

Lemma transsym : forall x y z : A, x = y -> x = z -> y = z.

Lemma eqneq : forall x y z : A, x = y -> ~ (x = z) -> ~ (y = z).

Lemma symneq : forall x y : A, ~(x = y) -> ~(y = x).

Lemma transneq : forall x y z : A, ~(x = y) -> ~(y = z) -> ~(x = z).








(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 1 (Propositional logic)
    published 10/10/11, deadline 18/10/11, 18:00 electronic submission

    Use
    $ cw submit ex01.v
    on one of the CS servers
    then look for the coursework 412 labelled 'g52cfr coursework 1' 
    and enter the associated code.

    Multiple submissions are allowed, up to the deadline.

    Try to fill in the missing proofs, using only the basic tactics presented
    in the first lectures (i.e. exact, intro(s), apply, destruct, left, right, split, assert).
    Do not use auto or tauto. Do not use any libraries.

    Note that not all the propositions below are provable!
    Comment out the ones, which you think are not provable and 
    mark them with the words "not provable", if you are sure.

**)

Section Ex1.

Variables P Q R : Prop.

Lemma ex01 : P -> Q -> P.

Lemma ex02 : (P -> Q -> R) -> (P -> Q) -> P -> R.

Lemma ex03 : (P -> Q) -> P /\ R -> Q /\ R.

Lemma ex04 : (P -> Q) -> ~P -> ~Q.

Lemma ex05 : (P -> Q) -> ~~P -> ~~Q.

Lemma ex06 : ~( P <-> ~P ).

Lemma ex07 : ~(P \/ Q) <-> ~P /\ ~Q.

Lemma ex08 : ~(P /\ Q) <-> ~P \/ ~Q.

(** Additional question:
    If we are allowed to use classical logic, i.e. the axiom classic : P \/ ~P
    then which of the previously unprovable statements become provable?
    Copy the appropriate lemma(s) down here and prove it(them) using classic.
*)
Require Import Coq.Logic.Classical.


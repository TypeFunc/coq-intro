(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 1 (Propositional logic)
    published 10/10/11, deadline 18/10/11, 12:00 electronic submission

    Use
    $ cw submit ex01.v
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

Section Ex1.

Variables P Q R : Prop.

Lemma ex01 : P -> Q -> P.
intros p q.
exact p.
Qed.

Lemma ex02 : (P -> Q -> R) -> (P -> Q) -> P -> R.
intros pqr pq p.
apply pqr.
exact p.
apply pq.
exact p.
Qed.

Lemma ex03 : (P -> Q) -> P /\ R -> Q /\ R.
intros pq pr.
destruct pr as [p r].
split.
apply pq.
exact p.
exact r.
Qed.

(*
Lemma ex04 : (P -> Q) -> ~P -> ~Q.
not provable.
*)

Lemma ex05 : (P -> Q) -> ~~P -> ~~Q.
intros pq nnp nq.
apply nnp.
intro p.
apply nq.
apply pq.
exact p.
Qed.

Lemma ex06 : ~( P <-> ~P ).
intro h.
destruct h as [h1 h2].
cut P.
intro p.
apply h1.
exact p.
exact p.
apply h2.
intro p.
apply h1.
exact p.
exact p.
Qed.

Lemma ex07 : ~(P \/ Q) <-> ~P /\ ~Q.
split.
  (* -> *)
  intro pq.
  split.
    (* ~P *)
    intro p.
    apply pq.
    left.
    exact p.
    (* ~Q *)
    intro q.
    apply pq.
    right.
    exact q.
  (* <- *)
  intro pq.
  intro pvq.
  elim pq.
  intros np nq.
  case pvq.
  exact np.
  exact nq.
Qed.

(*
Lemma ex08 : ~(P /\ Q) <-> ~P \/ ~Q.
not provable.
*)


(** Additional question:
    If we are allowed to use classical logic, i.e. the axiom classic : P \/ ~P
    then which of the previously unprovable statements become provable?
    Copy the appropriate lemma(s) down here and prove it(them) using classic.
*)
Require Import Coq.Logic.Classical.

Lemma ex08 : ~(P /\ Q) <-> ~P \/ ~Q.
split.
  (* -> *)
  intro npq.
  case (classic (~ P \/ ~ Q)).
   intro npnq.
   exact npnq.
   intro nnpnq.
   left.
   intro p.
   apply nnpnq.
   right.
   intro q.
   apply npq.
   split.
   exact p.
   exact q.
   (* <- *)
   intros npnq npq.
   elim npq.
   intros p q.
   case npnq.
   intro np.
   apply np.
   exact p.
   intro nq.
   apply nq.
   exact q.
Qed.
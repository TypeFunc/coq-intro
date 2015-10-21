(** This file collects Coq code for Andrej Bauer's tutorials at
    http://www.youtube.com/watch?v=tZRAFKIv6Js&feature=share&list=PLDD40A96C2ED54E99
*)


Module LEM.

(** How to use Coq with Proof General *)

Definition pierce := forall (p q : Prop), ((p -> q) -> p) -> p.
Definition lem := forall (p : Prop), p  \/ ~ p.

Theorem pierce_equiv_lem : pierce <-> lem.
Proof. 
  unfold pierce, lem.
  firstorder.
  apply H with (q := ~(p \/ ~p)).
  (* At this point, Coq tells us we need to prove the hypothesis 
     of Pierce's Law holds, that is (p -> q) -> p, where p:= p\/~p
     and q := ~(p \/ ~p).  This suffices because, by Pierce's Law, this
     will imply our desired conclusion p (i.e. p \/ ~p) holds.
   *)
  tauto.

  (* Now we must prove the converse: lem -> pierce *)
  destruct (H p).
  assumption.
  tauto.
Qed.

Print pierce_equiv_lem.

End LEM.



Module Frobenius.

(** The Frobenius rule for conjunction.
    From Andrej Bauer's YouTube tutorial at http://youtu.be/z861PoZPGqk
*)
Theorem frobenius_conj (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).
Proof.
  split.                   (* Split the iff into two parts. *)
  intros [y [H1 H2]].      (* Introduce an instance of the antecedent. *)
                           (* That is, y in A such that q and p y. *)
  split.                   (* Split the consequent. *)
  assumption.              (* First subgoal is q, but that is a hyp. *)
  exists y.                (* For next subgoal, exists x : A, p x, plug in y. *)
  assumption.              (* Then p y is an hypothesis. *)
  intros [H1 [y H2]].
  exists y.
  split.
  assumption.
  assumption.
Qed.

Check frobenius_conj.
Print frobenius_conj.
(**
    Remarks:
    1. The last subgoal was q /\ p y, and these both appeared 
       as hypotheses above the line, so you can just type auto 
       and Coq will complete the proof.

    2. Coq can prove the Frobenius Theorem automatically.  
    Try this instead of the proof above:

        Proof.
          firstorder.
        Qed.
  
    Then, to see what the resulting proof looks like, evaluate the line

        Print frobenius_conj.
*)


(** The Frobenius rule for disjunction.
    From Andrej Bauer's YouTube tutorial at
    http://www.youtube.com/watch?v=tZRAFKIv6Js&feature=share&list=PLDD40A96C2ED54E99&index=4
*) 
Theorem frobenius_disj_first_try (A : Set) (p : A -> Prop) (q : Prop) :
  (forall x : A, q \/ p x) <-> (q \/ forall x : A, p x).
Proof.
  firstorder.
  (* At this point, we are stuck, but notice that there is only one subgoal.
     This is because Coq was able to prove one direction of the iff using
     first order reasoning.  The -> direction remains to be proved and, in fact,
     can't be proved without classical reasoning; i.e., it requires the lem.
     So, we abort this attempt, and below we use lem to prove the -> direction.
   *)
Abort.

Definition lem := forall p, p \/ ~p.
Print lem.

Definition frobenius_disj := forall (A : Set) (p : A -> Prop) (q : Prop),
  (forall x : A, q \/ p x) <-> (q \/ forall x : A, p x).

Theorem lem_to_frobenius_disj_first_try : lem -> frobenius_disj.
Proof.
  unfold lem.
  unfold frobenius_disj.
  firstorder.  (* Again, first order leaves us with one direction to prove.
                  but now we have an additional assumption.  *)
  destruct (H q). 
  (* When faced with proving a disjunction, we can choose which side to prove: *)
  left.
  assumption.
  right.
  intros x.
  destruct (H0 x).
  (* At this point, we have two contradicting assumptions, 
     H1: ~q and H2: q, so anything follows. Handle this like so: *)
  elim H1.
  assumption.
  assumption.
Qed.

Check lem_to_frobenius_disj_first_try.
Print lem_to_frobenius_disj_first_try.

(**
    To recap, `firstorder` doesn't work because the implication from left to right in
    this case requires lem. When a proof requires classical reasoning, Coq will not
    do it automatically.  Coq only does intuitionistic logic automatically. This makes
    it *more* general, not less, since you can always add the classical lem hypothesis.
*)

(** The foregoing was a slow proof and can be cleaned up.  In particular, wenen we
    split a proof into cases and then apply the same reasoning to each case, it's 
    better to use the semicolon, rather than repeating ourselves. For example, in 
    the proof above, both branches were handled by first order reasoning, and we 
    can let Coq complete the proof for each branch. Below is the cleaned up proof. *)

Theorem lem_to_frobenius_disj : lem -> frobenius_disj.
Proof.
  unfold lem, frobenius_disj.
  firstorder.  (* Again, first order leaves us with one direction to prove.
                  but now we have an additional assumption.  *)
  destruct (H q); firstorder. 
Qed.

(* The proof of the converse is a little harder. *)
Theorem frobenius_disj_to_lem: frobenius_disj -> lem.
Proof.
  unfold frobenius_disj, lem.
  firstorder.
  destruct (H {_ : unit | p} (fun _ => False) p).   (* {_ : unit | p} is empty if p false *)
  clear H1.
  cut (p \/ ({_ : unit | p} -> False)).    (* insert an intermediate step *)
(*  cut (p \/ (sig (fun _ : unit => p) -> False)).  *)  (* insert an intermediate step *) 
  (* In general, when trying to prove A => B, if we want
     to first prove A => C and then C => B, we use cut. *)

  (* Coq splits into subgoals: prove intermediate thing implies end goal then prove intermediate thing.
     Coq turned the antecedent of the result of our destruct statement 
          destruct (H {_ : unit | p} (fun _ => False) p). 
      into the implication
          ( {_ : unit | p} -> p \/ False)
      because we have a forall where we quantify over a set and the quantified statement doesn't depend on the variable.
  *)
  intros [K1 | K2].   (* two branches of the disjunction *)
  left; assumption.
  right.
  intro.
  apply K2.
  exists tt.
  assumption.
  (* Now we must prove the intermediate step, which is the consequent of G, so... *)
  apply H0.
  (* ...and the resulting subgoal is to prove the antecendent of G. *)
  intros [u J].
  left; assumption.
Qed.  


(* sig (fun _ : unit => p) is the set of all elements of type unit which satisfy p. *)


(* How to interpret the mixing of types: Set -> Prop *)
Parameter S : Set.
Parameter q r: Prop.
Lemma map_set_to_prop : forall x : S, q.  
(** Results in S -> q, where we equate q with the set of all proofs of q.
    So by S -> q, Coq means the function type from elements of S to proofs of q."
 *)

(** Implication is a special case of for all. *)
Lemma map_proofs_to_prop : forall u : q, r.    
(** Says "for all proofs u of q, I can produce a proof of r." 
    This is the same as q -> r. *)

(* You could also write this as *)
Lemma map_proofs_to_prop2 : forall _ : q, r.    

Definition A := {y : S | q}.  (* the set of all elements of type S that satisfy q *)
Print A.

End Frobenius

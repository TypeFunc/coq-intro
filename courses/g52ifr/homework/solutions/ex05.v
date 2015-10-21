(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 5 (Lists)
    published 15/11/11, deadline 22/11/11, 18:00 electronic submission

    Use
    $ cw submit ex05.v
    on one of the CS servers
    then look for the coursework ??? labelled 'g52cfr coursework 5' 
    and enter the associated code.

    Multiple submissions are allowed, up to the deadline.

    Try to fill in the missing proofs, using only the basic tactics presented
    in the lectures.
    Do not use any additional libraries.

**)

Section Ex05.

(** We are using all the results from the lecture. *)
Load Lists.
Set Implicit Arguments.
Implicit Arguments nil [A].
Infix "::" := cons (at level 60, right associativity).
Infix "++" := app (right associativity, at level 60).

(** 1 **)

Section Frev.
(* The naive implementation of reverse is quite inefficient because
   the list is traversed many times (so indeed it has a quadratic 
   complexity). The following (fast) implementation of reverse is 
   better and has only linear complexity. It uses an axilliary function
   which accumulates the result in a 2nd paramenter which is returned
   when the end of the list is reached.

   Your task is to show that the fast implementation does the same
   as the original one. This will require to prove some lemmas. 
   
   Hint: frev_aux satisfies the following property:
         frev_aux l l' = rev l ++ l'
*)

Fixpoint frev_aux (A : Set)(l acc : list A) : list A :=
  match l with
  | nil => acc
  | a :: l' => frev_aux l' (a::acc)
  end.

(* frev is defined by initializing the accumulator with nil. *)

Definition frev (A:Set)(l:list A) : list A := 
  frev_aux l nil.

(* a quick test: *)

Eval compute in frev_aux (1::2::3::nil).

Lemma snoc_app_lem : forall (A:Set)(l l':list A)(a:A), (snoc l a) ++ l' = l ++ (a::l').
induction l.
  reflexivity.
  intros.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma frev_aux_lem : forall (A:Set)(l l':list A),frev_aux l l' = rev l ++ l'.
induction l. 
  reflexivity.
  intros.
  simpl.
  eapply trans_eq.  
    apply IHl.
    rewrite <- snoc_app_lem.
    reflexivity.
Qed.

(* Our goal is to show that rev is doing the same as frev: *)

Lemma rev_lem : forall (A:Set)(l:list A), rev l = frev l.
intros.
unfold frev.
rewrite frev_aux_lem.
rewrite app_l_nil.
reflexivity.
Qed.

End Frev.

(** 2 **)
Section perm.

(* We say that a list is a permutation of another list
   if one list can be obtained from the other by rearranging
   the elements. One way to specify this is to say is using
   a function which counts occurences and then a list is
   a permutation if the number of all elements is the same.
*)

Fixpoint count (n:nat)(ms:list nat) {struct ms} : nat :=
  match ms with
  | nil => 0
  | m::ms' => let cn := count n ms' 
              in if eqnat n m then S cn else cn
  end.

Definition Perm (ns ms:list nat) := forall n:nat,count n ns=count n ms.

(* The first task is to show that Perm is an equivalence
   relation, i.e. that it is reflexive, symmetric and 
   transitive.
*)

Lemma refl_perm : forall ns:list nat,Perm ns ns.
unfold Perm.
intros.
reflexivity.
Qed.

Lemma trans_perm : forall ls ms ns:list nat,Perm ls ms -> Perm ms ns -> Perm ls ns.
unfold Perm.
intros.
  transitivity (count n ms).
  apply H.
  apply H0.
Qed.

Lemma sym_perm : forall ms ns : list nat, Perm ms ns -> Perm ns ms.
intros ms ns h n.
rewrite h.
reflexivity.
Qed.

Lemma cons_perm : forall (n:nat)(ms ns:list nat),Perm ms ns -> Perm (n::ms) (n::ns).
unfold Perm.
intros.
  simpl.
  rewrite H.
  case (eqnat n0 n).
    reflexivity.
    reflexivity.
Qed.

Lemma snoc_perm : forall (ns:list nat)(n:nat),Perm (n::ns) (snoc ns n).
induction ns.
  intros.
  apply refl_perm.
  (* cons *)
  unfold Perm.
  intros.
  simpl.
  unfold Perm in IHns.
  rewrite <- IHns.
  simpl.
  case (eqnat n0 n).
    case (eqnat n0 a).
      reflexivity.
      reflexivity.
      reflexivity.
Qed.

(* 
   Show that rev produces a permutation of the input list.
   This will require a lemma about snoc.
*)

Theorem rev_perm : forall (ns:list nat),Perm ns (rev ns).
induction ns.
  apply refl_perm.
  simpl.
  eapply trans_perm.
  apply cons_perm.
  apply IHns.
  apply snoc_perm.
Qed.

Lemma insert_perm : forall (ns:list nat)(n:nat), Perm (n::ns) (insert n ns).
induction ns.
  intros.
  apply refl_perm.
  intros.
  simpl.
  case (leqb n a).
    apply refl_perm.
    eapply trans_perm.
    instantiate (1 := a::n::ns).
    unfold Perm.
    intros.
    simpl.
    case (eqnat n0 n).
      case (eqnat n0 a).
      reflexivity.
      reflexivity.
      case (eqnat n0 a).
      reflexivity.
      reflexivity.
    apply cons_perm.
    apply IHns.
Qed.

(* Show that the sort function produces a permutation
   of the input list. This will require a lemma about
   insert.
*)

Theorem sort_perm : forall ms:list nat,Perm ms (sort ms).
induction ms.
  apply refl_perm.
  eapply trans_perm.
    apply cons_perm.
    apply IHms.
    simpl.
    apply insert_perm.
Qed.

End perm.

End Ex05.
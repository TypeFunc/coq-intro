(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 5 (Lists)
    published 14/11/11, deadline 22/11/11, 18:00 electronic submission

    Use
    $ cw submit ex05.v
    on one of the CS servers
    then look for the coursework 432 labelled 'g52cfr coursework 5' 
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
   which accumulates the result in a 2nd parameter which is returned
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

(* Our goal is to show that frev is doing the same as rev: *)

Lemma rev_lem : forall (A:Set)(l:list A), rev l = frev l.

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

Lemma trans_perm : forall ls ms ns:list nat,Perm ls ms -> Perm ms ns -> Perm ls ns.

Lemma sym_perm : forall ms ns : list nat, Perm ms ns -> Perm ns ms.

(* 
   Show that rev produces a permutation of the input list.
   This will require a lemma about snoc.
*)

Theorem rev_perm : forall (ns:list nat),Perm ns (rev ns).

(* Show that the sort function produces a permutation
   of the input list. This will require a lemma about
   insert and maybe more.
*)

Theorem sort_perm : forall ms:list nat,Perm ms (sort ms).

End perm.

End Ex05.
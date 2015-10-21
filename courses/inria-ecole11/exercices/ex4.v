Require Import Arith.
Require Import List ZArith.
Require Import Bool.
(* We first want to prove that our definition of add satisfies commutativity. *)

Fixpoint add n m := 
  match n with 0 => m | S p => add p (S m) end.

Lemma addnS : forall n m, add n (S m) = S (add n m).
induction n.
  intros m; simpl.
  reflexivity.
intros m; simpl.
now apply IHn.
Qed.

(* Q1. Prove the following two theorems: beware that you will probably need
  addnS. *)
Lemma addn0 : forall n, add n 0 = n.
Admitted.

Lemma add_comm : forall n m, add n m = add m n.
Admitted.

(* Q2. Now state and prove the associativity of this function. *)

(* Q3. Now state and prove a theorem that expresses that the add function
  returns the same result as the addition available in the loaded libraries
  (given by function plus) *)

(* Note that the theorems about commutativity and associativity could be
  consequences of add_plus. *)

(* Programs about lists.  *)


Fixpoint multiplicity (n : Z)(l : list Z) : nat  := 
  match l with 
    nil => 0%nat 
  | a :: l' => 
    if Zeq_bool n a then S (multiplicity n l') 
    else multiplicity n l' 
  end. 

Definition is_perm (l l'  : list Z)  := 
  forall n, multiplicity n l = multiplicity n l'.

(* Q4. Show the following theorem :  *)

Lemma multiplicity_app  (x : Z) (l1 l2 : list Z) : 
  multiplicity x (l1 ++ l2) = multiplicity x l1 + multiplicity x l2.
Admitted.


(* Q5. State and prove a theorem that expresses that element counts are
  preserved by reverse. *)


(* Q6. Show the following theorem.  You will probably have an occasion
  to use the ring tactic *)


Lemma is_perm_transpose x y l1 l2 l3 : 
  is_perm (l1 ++ x::l2 ++ y::l3) (l1 ++ y :: l2 ++ x :: l3).
Admitted.


(* Q5 : What does this function do? *)
Fixpoint mask (A : Type)(m : list bool)(s : list A) {struct m} :=
  match m, s with
  | b :: m', x :: s' => if b then x :: mask A m' s' else mask A m' s'
  | _, _ => nil
  end.

Implicit Arguments mask.

(* Q6 Prove that : *)
Lemma mask_cat A m1 (s1 : list A) :
    length m1 = length s1 ->
  forall m2 s2, mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
Admitted.
Require Import List.

(* Exercise 1 *)
(* Use an inductive predicate to characterize lists with an even length.
(* Name this predicate even_len *)

(* insert your solution here. *)

Implicit Arguments even_len.

Lemma even_len_example :
   forall a : nat, even_len (a::(2*a)::(3*a)::(4*a)::nil).
Admitted.

(* Exercise 2 *)
(* Define an inductive predicate named transp to express that a list l1 
   is the same as a list l2 where two consecutive elements have been
   transposed.
   - use one constructor to express that the first two elements of the
     list have been transposed and the rest is the same for the two lists.
     For instance (transp (1::3::2::4::nil) (3::1::2::4::nil)) should be
     provable using this constructor.
   - use one constructor to express that the two lists have the same first
     element, but their tails exhibit a transposition.
     For instance (transp (1::3::2::4::nil) (1::2::3::4::nil)) should have
     a proof that starts by using this constructor.
     This predicate should have three arguments: a type A and two lists of
     type A.  Make the type A an implicit argument using the command
     "Implicit Arguments transp." *)


Lemma transp_ex : transp (1::3::2::4::nil) (1::2::3::4::nil).
Admitted.

(* Exercise 3 *)
(* Define an inductive relation named permutation that is satisfied by l1 l2 if
   one of the following cases is satisfied:
   1/ l1 and l2 are the same
   2/ l1 is a transposition of l3 and l3 is a permutation of l2.
   Again, this relation should be polymorphic, and you should add an
   implicit argument declaration. *)


(* Exercise 4 *)
Lemma permutation_refl : forall (A : Type) (l1 : list A), permutation l1 l1.
Admitted.

Lemma permutation_transitive : forall (A : Type) (l1 l2 l3 : list A),
  permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.
Admitted.

Lemma transp_sym : forall A (l1 l2:list A), transp l1 l2 -> transp l2 l1.
Admitted.

Lemma permutation_sym : forall (A : Type) (l1 l2 : list A), permutation l1 l2 -> permutation l2 l1.
Admitted.

Lemma permutation_C : forall A (a:A) l1 l2, permutation l1 l2 -> permutation (a::l1) (a::l2).

(* The following function definitions describe a sorting algorithm
   (insertion sort) *)

Fixpoint insert x l :=
  match l with 
    nil => x::nil
  | y::tl => if leb x y then x::l else y::insert x tl
  end.

Fixpoint sort l :=
  match l with
    nil => nil
  | x::tl => insert x (sort tl)
  end.

(* Now we wish to prove that sorting a list returns an output that
   satisfies the permutation relation with the input. *)

Lemma insert_permutation : forall x l, permutation (insert x l) (x::l).
Admitted.

Lemma sort_permutation : forall l, permutation (sort l) l.
Admitted.

(* Now if you are courageous enough, you should describe what a sorted
   list is (for instance using an inductive predicate) and show
   that the output of sort is a sorted list.  You will need concepts
   introduced in lesson 7, though! *)

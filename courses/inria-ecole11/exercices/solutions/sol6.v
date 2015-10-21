Require Import List Arith.

(* Exercise 1 *)
(* Use an inductive predicate to characterize lists that have an even length. *)
Inductive even_len (A : Type) : list A -> Prop :=
  ev_len_nil : even_len A nil
| ev_len_CC : forall a b : A, forall l, even_len A l -> even_len A (a::b::l).

Implicit Arguments even_len.

Lemma even_len_example :
   forall a : nat, even_len (a::(2*a)::(3*a)::(4*a)::nil).
intros a; repeat apply ev_len_CC; apply ev_len_nil.
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
Inductive transp (A : Type) : list A -> list A -> Prop :=
  transp_h : forall a b l, transp A (a::b::l) (b::a::l)
| transp_C : forall a l1 l2, transp A l1 l2 -> transp A (a::l1) (a::l2).

Implicit Arguments transp.

Lemma transp_ex : transp (1::3::2::4::nil) (1::2::3::4::nil).
apply transp_C, transp_h.
Qed.

(* Exercise 3 *)
(* Define an inductive relation named permutation that is satisfied by l1 l2 if
   one of the following cases is satisfied:
   1/ l1 and l2 are the same
   2/ l1 is a transposition of l3 and l3 is a permutation of l2.
   Again, this relation should be polymorphic. *)

Inductive permutation (A : Type) : list A -> list A -> Prop :=
  perm_refl : forall l, permutation A l l
| perm_step : forall l1 l2 l3, transp l1 l2 -> permutation A l2 l3 -> permutation A l1 l3.

Implicit Arguments permutation.

(* Exercise 4 *)
Lemma permutation_refl : forall (A : Type) (l1 : list A), permutation l1 l1.
apply perm_refl.
Qed.

Lemma permutation_transitive : forall (A : Type) (l1 l2 l3 : list A),
  permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.
intros A l1 l2 l3 H; revert l3; induction H.
  tauto.
intros l4 p34.
(* This also works:
assert (tmp := perm_step); firstorder. *)
apply perm_step with l2.
  assumption.
apply IHpermutation.
assumption.
Qed.

Lemma transp_sym : forall A (l1 l2:list A), transp l1 l2 -> transp l2 l1.
intros A l1 l2 H; induction H.
apply transp_h.
apply transp_C.
assumption.
Qed.

Lemma permutation_sym : forall (A : Type) (l1 l2 : list A), permutation l1 l2 -> permutation l2 l1.
intros A l1 l2 H; induction H.
  constructor.
apply permutation_transitive with l2.
  assumption.
apply perm_step with l1.
apply transp_sym.
exact H.
apply permutation_refl.
Qed.

Lemma permutation_C : forall A (a:A) l1 l2, permutation l1 l2 -> permutation (a::l1) (a::l2).
intros A a l1 l2 H; induction H.
apply permutation_refl.
apply perm_step with (a::l2).
apply transp_C.
assumption.
assumption.
Qed.

(* The following function definitions describe a sorting algorithm   (insertion sort) *)
Fixpoint insert x l :=
  match l with 
    nil => x::nil
  | y::tl => if leb x y then x::l else y::insert x tl
  end.

Fixpoint sort l :=
  match l with
    nil => nil
  | x::tl => insert x tl
  end.

(* Now we wish to prove that sorting a list returns an output that   satisfies the permutation relation with the input. *)
Lemma insert_permutation : forall x l, permutation (insert x l) (x::l).
intros x l; induction l.
  simpl; apply permutation_refl.
simpl.
case (leb x a).
  apply permutation_refl.
apply permutation_transitive with (a::x::l).
apply permutation_C.
assumption.
apply perm_step with (x::a::l).
apply transp_h.
apply permutation_refl.
Qed.

Lemma sort_permutation : forall l, permutation (sort l) l.
induction l.
 apply permutation_refl.
simpl.
apply insert_permutation.
Qed.

(* Now if you are courageous enough, you should describe what a sorted   list is (for instance using an inductive predicate) and show   that the output of sort is a sorted list. *)

Inductive sorted : list nat -> Prop :=
  snil : sorted nil
| s1 : forall x, sorted (x::nil)
| s2 : forall x y l, sorted (y::l) -> x <= y ->
    sorted (x::y::l).

Inductive choice_heads (x : nat) : list nat -> list nat -> Prop :=
  ch1 : forall l1 l2, choice_heads x l1 (x::l2)
| ch2 : forall y l1 l2, choice_heads x (y::l1)(y::l2).

Lemma insert_sorted : forall x l, sorted l -> sorted (insert x l).
assert (forall x l, sorted l -> sorted (insert x l) /\ (forall y, sorted (y::l) -> sorted (insert x (y::l)))).
induction l.
intros _; split;[constructor | intros y syl].
simpl; case_eq (leb x y); intros tst.
now apply s2;[constructor | apply leb_complete].
now apply s2;[constructor | apply lt_le_weak; apply leb_complete_conv].
intros sal.
assert (sl : sorted l) by (inversion sal;trivial; constructor).
split.
  now firstorder.
 intros y syal.
 change (sorted (if leb x y then x::y::a::l else
                    y::(insert x (a::l)))).
case_eq (leb x y); intros tst.
apply s2.
 assumption.
now apply leb_complete.
apply IHl in sl; destruct sl as[IHl1 IHl2].
apply IHl2 in sal.
revert sal; simpl; case (leb x a); intros tst2.
now apply s2;[| apply lt_le_weak; apply leb_complete_conv].
now apply s2;[ | inversion syal].
now firstorder.
Qed.

(* We consider the discrete plan the coordinate system of which 
    is based on Z *)
Require Import List.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.

(* Define a record type for points in the plane *)

Record Point : Type :=
 {Point_x : Z;
  Point_y:Z}.

Definition Point_O := Build_Point 0 0.

Definition translate (dx dy:Z) (P : Point) :=
  Build_Point (Point_x P + dx) (Point_y P + dy).

(* Define a boolean function Point_eqb for deciding equality between
Points *)


Definition Point_eqb (P P':Point) :=
   Zeq_bool (Point_x P) (Point_x P') &&
   Zeq_bool (Point_y P) (Point_y P').

(* Prove the correctness of Point_eqb *)

Lemma Point_eqb_correct : forall p p', Point_eqb p p' = true <->
                                       p = p'.
destruct p;destruct p';simpl;split.
 unfold Point_eqb;simpl;  rewrite andb_true_iff; destruct 1.
 repeat rewrite <- Zeq_is_eq_bool in *.
 rewrite H, H0;reflexivity.
injection 1;intros H0 H1;rewrite H0, H1.
 unfold Point_eqb.
 simpl.
 rewrite andb_true_iff;repeat rewrite <- Zeq_is_eq_bool.
auto.
Qed.


(* Let us define a type for routes in the plane *)

Inductive direction : Type := North | East | South | West.

Definition route := list direction.

(* Define a function move : Point -> route -> Point :
  move P r follows the route r starting from P *)

Fixpoint move (P:Point) (r:route) : Point :=
 match r with
 | nil => P
 | North :: r' => move (translate 0 1 P) r'
 | East :: r' => move (translate 1 0 P) r'
 | South :: r' => move (translate 0 (-1) P) r'
 | West :: r' => move (translate (-1) 0 P) r'
 end.




(* We consider that two routes are "equivalent" if they define
  the same moves. For instance, the routes
  East::North::West::South::East::nil and East::nil are equivalent *)

Definition route_equiv : relation route :=
  fun r r' => forall P, move P r = move P r'.

Example Ex1 : route_equiv (East::North::West::South::East::nil) (East::nil).
Proof.
intro P;destruct P.
simpl.
unfold translate;simpl.
f_equal.
ring.
ring.
Qed.


Lemma route_equiv_refl : reflexive _ route_equiv.
Proof.
 intros r p;reflexivity.
Qed.

Lemma route_equiv_sym : symmetric _ route_equiv.
Proof.
 intros r r' H p.
 symmetry;apply H.
Qed.


Lemma route_equiv_trans : transitive _ route_equiv.
Proof.
 intros r r' r'' H H' p.
 rewrite H.
 apply H'.
Qed.


(* cut here for class 8 *)

Instance route_equiv_Equiv : Equivalence  route_equiv.
split.
apply route_equiv_refl.
apply route_equiv_sym.
apply route_equiv_trans.
Qed.



(* Prove that cons and app are Proper wrt route_equiv *)
Require Import Morphisms.

Instance cons_route_Proper (d:direction): 
    Proper (route_equiv ==> route_equiv) (cons d) .
intros r r' H P.
destruct d;simpl;rewrite H;auto.
Qed.


Instance app_route_Proper : Proper (route_equiv ==>route_equiv==>route_equiv)
 (@app direction).


 (* A useful lemma *)

 Lemma route_compose : forall r r' P, move P (r++r') = move (move P r) r'.
 induction r;simpl;auto.
 destruct a;
 intros;rewrite IHr;auto.
Qed.

 
 intros r r' H r'' r''' H' P.
 repeat rewrite route_compose.
 rewrite H.
 rewrite H'.
 auto.
Qed.


 Class EMonoid {A:Type}(E_eq :relation  A)(dot : A->A->A)(one : A):={
  E_rel :> Equivalence E_eq; 
  dot_proper :> Proper (E_eq ==> E_eq ==> E_eq) dot; 
  E_dot_assoc : forall x y z:A, E_eq (dot x (dot y z)) (dot (dot x y) z);
  E_one_left : forall x, E_eq (dot one  x) x;
  E_one_right : forall x, E_eq (dot x  one) x}.


Instance Route : EMonoid route_equiv (@app _) nil .
split.
apply route_equiv_Equiv.
apply app_route_Proper.
intros x y z P;repeat rewrite  route_compose.
 trivial.
 intros x  P;repeat rewrite  route_compose.
 trivial.
intros x  P;repeat rewrite  route_compose.
 trivial.
Qed.



(* (difficult) : prove the following lemma *)

Lemma move_translate : forall r P dx dy , move (translate dx dy P) r =
                                         translate dx dy (move P r).
induction r;simpl;auto.
destruct a;simpl.
  Lemma translate_comm : forall dx dy dx' dy' P,
    translate dx dy (translate dx' dy' P) =
    translate dx' dy' (translate dx dy P).
  unfold translate; simpl; intros; f_equal; ring.
 Qed.

intros;rewrite <- IHr;rewrite  (translate_comm );auto.
intros;rewrite <- IHr;rewrite  (translate_comm );auto.
intros;rewrite <- IHr;rewrite  (translate_comm );auto.
intros;rewrite <- IHr;rewrite  (translate_comm );auto.
Qed.

(* Prove the following corollary *)

Lemma route_equiv_Origin : forall r r', route_equiv r r' <->
                                        move Point_O r = move Point_O r'.
Proof.
split;intro H.
rewrite H;trivial.
intro P.
replace P with (translate (Point_x P) (Point_y P) Point_O).

repeat rewrite move_translate.
rewrite H;reflexivity.
destruct P;simpl.
unfold translate.
f_equal.
Qed.

(* Then build a boolean function for  deciding route equivalence ... *)

Definition route_eqb r r' := Point_eqb (move Point_O r) (move Point_O r').

(* ... and prove its correctness *)

Lemma route_equiv_equivb : forall r r', route_equiv r r' <->
                                        route_eqb r r' = true.
Proof.
 intros r r' ; rewrite route_equiv_Origin. 
unfold route_eqb.
rewrite Point_eqb_correct.
tauto.
Qed.


(* Now, prove simply our  Example *)



Example Ex1' : route_equiv (East::North::West::South::East::nil) (East::nil).
rewrite route_equiv_equivb;reflexivity.
Qed.

Lemma north_south_0 : forall r, route_equiv (North::South::r) r.
intro r; change (route_equiv ((North::South::nil)++ r) r).
setoid_replace (North :: South :: nil) with (@nil direction).
reflexivity.
rewrite route_equiv_equivb;reflexivity.
Qed.

Lemma north_south_simpl : forall r r', route_equiv (r++ North::South::r')
                                                   (r++r').
induction r.
simpl. intro r';rewrite north_south_0;reflexivity.
intros;simpl.
rewrite IHr.
reflexivity.
Qed.











 


  



(* We consider the discrete plan the coordinate system of which 
    is based on Z *)
Require Import List.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.

(* Define a record type for points in the plane *)

Record Point : Type :=
 {Point_x : Z;
  Point_y: Z}.

Definition Point_O := Build_Point 0 0.

Definition translate (dx dy:Z) (P : Point) :=
  Build_Point (Point_x P + dx) (Point_y P + dy).

(* Define a boolean function Point_eqb for deciding equality between
Points *)


(* Prove the correctness of Point_eqb *)


(* Let us define a type for routes in the plane *)

Inductive direction : Type := North | East | South | West.

Definition route := list direction.

(* We define a function move : Point -> route -> Point :
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

(* Prove the following equivalence.  Hint : you may use f_equal and ring
 tactics *)

Example Ex1 : route_equiv (East::North::West::South::East::nil) (East::nil).
Admitted.

(* Prove that route_equiv is reflexive, symmetric and transitive  *)

Lemma route_equiv_refl : reflexive _ route_equiv.
Admitted.

Lemma route_equiv_sym : symmetric _ route_equiv.
Admitted.


Lemma route_equiv_trans : transitive _ route_equiv.
Admitted.


(***** cut here  for class 8  ****)



Instance route_equiv_Equiv : Equivalence  route_equiv.
(* Do it  yourself *)
Admitted.


(* Prove that cons and app are Proper wrt route_equiv *)
Require Import Morphisms.

Instance cons_route_Proper (d:direction): 
    Proper (route_equiv ==> route_equiv) (cons d) .
(* do it yourself *)
Admitted.

 Lemma route_compose : forall r r' P, move P (r++r') = move (move P r) r'.
(* do it yourself *)
Admitted.


Instance app_route_Proper : Proper (route_equiv ==>route_equiv==>route_equiv)
 (@app direction).
(* do it yourself *)
Admitted.

(* Monoids w.r.t. some equivalence relation *)

Class EMonoid {A:Type}(E_eq :relation  A)(dot : A->A->A)(one : A):={
  E_rel :> Equivalence E_eq; 
  dot_proper :> Proper (E_eq ==> E_eq ==> E_eq) dot; 
  E_dot_assoc : forall x y z:A, E_eq (dot x (dot y z)) (dot (dot x y) z);
  E_one_left : forall x, E_eq (dot one  x) x;
  E_one_right : forall x, E_eq (dot x  one) x}.


Instance Route : EMonoid route_equiv (@app _) nil .
(* do it yourself *)
Admitted.



(* (difficult) : prove the following lemmas *)
  Lemma translate_comm : forall dx dy dx' dy' P,
    translate dx dy (translate dx' dy' P) =
    translate dx' dy' (translate dx dy P).
  Proof.
  (* do it yourself *)
  Admitted.

Lemma move_translate : forall r P dx dy , move (translate dx dy P) r =
                                         translate dx dy (move P r).
 (* do it yourself *)
  Admitted.

Lemma route_equiv_Origin : forall r r', route_equiv r r' <->
                                        move Point_O r = move Point_O r'.
Proof.
(* difficult *) 
Admitted.

(* Then build a boolean function route_equivb for  deciding route equivalence ... *)


(* ... and prove its correctness *)


(* Now, we can prove our previous  example by reflexion, (using route_equivb) 
  *)

Example Ex1' : route_equiv (East::North::West::South::East::nil) (East::nil).
Admitted.


(* Using the tactics rewrite, setoid_replace, etc. prove the following
   lemmas *)

Lemma north_south_0 : forall r, route_equiv (North::South::r) r.
Admitted.

Lemma north_south_simpl : forall r r', route_equiv (r++ North::South::r')
                                                   (r++r').
Admitted.






 


  



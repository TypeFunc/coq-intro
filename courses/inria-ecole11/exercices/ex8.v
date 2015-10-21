

(* Exercise 1 *)
(* Consider the following definitions *)
(* Note: any theorem --- either proven or admitted --- can be used for proving the following
  ones  *)

Require Import Omega.

Inductive Even : nat -> Prop :=
|  Ev0: Even 0
|  Ev2 : forall n, Even n -> Even (S (S n)).

Definition Odd n := Even (S n).


(* Prove the following lemmas (remove the Admitted) *)


Lemma E6: Even 6.
Admitted.

Lemma O7 : Odd 5.
Admitted.

Lemma E_double : forall n:nat, Even (2*n).
Admitted.

Lemma not_E1 : ~ Even 1.
Admitted.


Lemma Even_SS_inv : forall n, Even (S (S n)) -> Even n.
Admitted.


Lemma Odd_not_Even : forall n, Odd n -> ~ Even n.
Admitted.

Lemma Even_not_Odd : forall n, Even n -> ~ Odd n.
Admitted.

Lemma Even_double : forall n, Even n -> exists p:nat, n = p + p.
Admitted.


Lemma Odd_S_double : forall n, Odd n -> exists p:nat, n = S( p + p).
Admitted.


(* Consider the following  function *)


Fixpoint evenb (n: nat):  bool :=
match  n with O => true
            | 1 => false
            | S (S p) => evenb p
end.

Lemma evenb_Sn : forall n:nat, evenb (S n) = negb (evenb n).
Admitted.


Lemma evenb_if : forall n:nat, if evenb n then Even n else Odd n.
Admitted.

Lemma evenb_iff : forall n, evenb n = true  <-> Even n.
Admitted.


Goal Even 560.
rewrite <- evenb_iff.
reflexivity.
Qed.

(* Exercise 2 *)

(* Consider the following definitions *)
Require Import Arith.


Definition Le (n p : nat) : Prop := exists q:nat, q + n = p.

Fixpoint LE (n p: nat): Prop :=
 match n, p with 0, _ => True
               | S _, 0 => False
               | S n', S p' => LE n' p'
 end.



(* Prove the following theorems  
  Note: any theorem --- either proven or admitted --- can be used for proving the following
  ones  *)

Lemma le_Le : forall n p, n <= p -> Le n p.
Admitted.

Lemma Le_le : forall n p, Le n p -> n <= p.
Admitted.

Lemma LE_n : forall n, LE n n.
Admitted.

Lemma LE_S : forall n p, LE n p -> LE n (S p).
Admitted.

Lemma le_LE : forall n p, n <= p -> LE n p.
Admitted.

Lemma LE_Le : forall n p, LE n p -> Le n p.
Admitted.

Require Import Max.


Lemma le_leb_iff : forall n p, n <= p <-> leb n p = true.

Lemma lt_lb_iff : forall n p, p < n <-> leb n p = false 

Use these lemmas for proving :

Lemma leb_max : forall n p, max n p = if leb n p then p else n.
(* 
Hint : execute the command 
SearchAbout [le max].

*)




(* Exercise  3 *)

(* Consider the following declarations : *)

Require Import List.

Section On_index.
Variable A : Type.
Variable eqAb : A -> A -> bool.

Inductive eqA_spec (a b:A):bool -> Prop :=
eqA_eq : forall Heq :a = b, eqA_spec a b true
|eqA_diff : forall Hdiff: a <> b , eqA_spec a b false.

Hypothesis eqAbP : forall a b, eqA_spec a b (eqAb a b).


(* Give an inductive definition of the predicate 
   is_nth a n l : Prop
  the maeaning of which is "a is the i-th element of the list l" *)


 
(* We now consider the following specification *)

Inductive index_spec (a:A)(l:list A):(option nat)->Prop :=
| success : forall i (Hsuccess:is_nth a i l), index_spec a l (Some i)
| failure : forall (Hfail : forall i, ~ is_nth a i l), index_spec a l None.


Definition index_ok (idx : A -> list A -> option  nat) :=
  forall a l, index_spec a l (idx a l).

(* Define a recursive function 
   index (a:A)(l:list A) : option  nat
   and prove your function is correct *)

(* Prove the following lemmas  *)

Lemma index_is_nth: forall a l i, index a l = Some i -> is_nth a i l.

Lemma is_nth_index: forall a l i, is_nth a i l -> exists j, index a l = Some j.





(* Exercise 4 : borrowed and adapted from B. Pierce's 
 course "Software Foundations"*)

(* We define the following toy language: *)
Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm.


(* Here is a big step evaluator for this language *)
Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      eval (tm_const n) n
  | E_Plus : forall t1 t2 n1 n2,
      eval t1 n1 ->
      eval t2 n2 ->
      eval (tm_plus t1 t2) (plus n1 n2).


(* Here is a small step evaluator for this language *)
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
        step (tm_plus (tm_const n1) (tm_const n2))
             (tm_const (plus n1 n2))
  | ST_Plus1 : forall t1 t1' t2,
        (step t1 t1')
     -> step (tm_plus t1 t2)
             (tm_plus t1' t2)
  | ST_Plus2 : forall n1 t2 t2',
        (step t2 t2')
     -> step (tm_plus (tm_const n1) t2)
             (tm_plus (tm_const n1) t2').

(*A few things to notice:
   
   * We are defining just a single reduction step, in which one
     tm_plus node is replaced by its value.

    * Each step finds the leftmost tm_plus node that is "ready to go"
      (both of its operands are constants) and reduces it. The first
      rule tells how to reduce this tm_plus node itself; the other two
      rules tell how to find it.

    * A term that is just a constant cannot take a step.
*)

(* Prove that: *)
Lemma step_plus_l : forall t1 t1' t2, step t1 t1' -> 
  step (tm_plus t1 t2) (tm_plus t1' t2).


(* Prove that evaluation is deterministic: *)
Lemma eval_det : forall t n1 n2, eval t n1 -> eval t n2 -> n1 = n2.


(* We can also prove that step is deterministic :
We must show that if x steps to both y1 and y2 then y1 and y2 are *)
(*equal. Consider the last rules used in the derivations of step x y1 *)
(*and step x y2.
    * If both are ST_PlusConstConst, the result is immediate.

    * It cannot happen that one is ST_PlusConstConst and the other is
      ST_Plus1 or ST_Plus2, since this would imply that x has the form
      tm_plus t1 t2 where both t1 and t2 are constants (by
      ST_PlusConstConst) AND one of t1 or t2 has the form tm_plus ....

    * Similarly, it cannot happen that one is ST_Plus1 and the other
      is ST_Plus2, since this would imply that x has the form tm_plus
      t1 t2 where t1 has both the form tm_plus t1 t2 and the form
      tm_const n.


    * The cases when both derivations end with ST_Plus1 or ST_Plus2
      follow by the induction hypothesis.
*)

Theorem step_deterministic :
 forall t t1 t2, step t t1 -> step t t2 -> t1 = t2.
Admitted.

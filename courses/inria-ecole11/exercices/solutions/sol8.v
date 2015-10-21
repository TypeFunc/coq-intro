

(* Exercise 1 *)
(* Consider the following definition *)
Require Import Arith.
Require Import Omega.

Inductive Even : nat -> Prop :=
|  Ev0: Even 0
|  Ev2 : forall n, Even n -> Even (S (S n)).

Definition Odd n := Even (S n).


(* Prove the following lemmas *)

Lemma E6: Even 6.
repeat constructor.
Qed.

Lemma O7 : Odd 5.
 unfold Odd;apply E6.
Qed.

Lemma E_double : forall n:nat, Even (2*n).
Proof.
 induction n as [| p IHp].
 simpl;constructor.
 replace (2 * S p) with (S (S (2 * p))).
 constructor;assumption.
omega.
Qed.

Lemma not_E1 : ~ Even 1.
intro H;inversion H.
Qed.


Lemma Even_SS_inv : forall n, Even (S (S n)) -> Even n.
intros n H;inversion H.
assumption.
Qed.


Lemma Odd_not_Even : forall n, Odd n -> ~ Even n.
Proof.
 intro n;induction n.
 intro H;inversion H.
 intros H H0.
 apply IHn.
 assumption.
 apply Even_SS_inv.
 assumption.
Qed.

Lemma Even_not_Odd : forall n, Even n -> ~ Odd n.
Proof.
 induction n.
 intros H H0;inversion H0.
 intros H H0.
 unfold Odd in H0.
 apply IHn.
  apply Even_SS_inv.
 assumption.
 assumption.
Qed.

Lemma Even_double : forall n, Even n -> exists p:nat, n = p + p.
intros n H;induction H.
exists 0.
reflexivity.
destruct IHEven as [p Hp].
exists (S p).
rewrite Hp;omega.
Qed.


Lemma Odd_S_double : forall n, Odd n -> exists p:nat, n = S( p + p).
intros n H;unfold Odd in H.
destruct (Even_double _ H).
destruct x.
discriminate H0.
simpl in H0;injection H0.
intro e;rewrite e.
exists x.
auto with arith.
Qed.


(* Consider the following  function *)


Fixpoint evenb (n: nat):  bool :=
match  n with O => true
            | 1 => false
            | S (S p) => evenb p
end.

Lemma evenb_Sn : forall n:nat, evenb (S n) = negb (evenb n).
intro n.
induction n.
reflexivity.
 change (evenb (S (S n))) with (evenb n).
 rewrite IHn.
 SearchRewrite (negb (negb _)).
 rewrite Bool.negb_involutive.
 reflexivity.
Qed.


Lemma evenb_if : forall n:nat, if evenb n then Even n else Odd n.
induction n.
simpl.

constructor.
case_eq (evenb (S n)).
intro H.
case_eq (evenb n).
intro H0.
rewrite evenb_Sn in H.
rewrite H0 in H;discriminate.
rewrite evenb_Sn in H.
intro H0;rewrite H0 in IHn.
assumption.

rewrite evenb_Sn.
destruct (evenb n).
intro.
unfold Odd.
constructor. assumption.
intro;discriminate.
Qed.

Lemma evenb_iff : forall n, evenb n = true  <-> Even n.
Proof.
 intro n;case_eq (evenb n).
 intro e.
 split;trivial.
 generalize (evenb_if  n);rewrite e.
 auto.
 intro e;generalize (evenb_if n).
 rewrite e.
 intro H;split.
 intro;discriminate.
 intro H0.
 destruct (Even_not_Odd n H0).
assumption.
Qed.


Goal Even 560.
rewrite <- evenb_iff.
reflexivity.
Qed.


(* Exercise 2 *)


(* Consider the following definitions *)

Definition Le (n p : nat) : Prop := exists q:nat, q + n = p.

Fixpoint LE (n p: nat): Prop :=
 match n, p with 0, _ => True
               | S _, 0 => False
               | S n', S p' => LE n' p'
 end.

(* Prove that Le and LE are logically equivalent to Coq's le predicate *)


Lemma le_Le : forall n p, n <= p -> Le n p.
Proof.
 intros n p H;induction H.
 exists 0;trivial.
 destruct IHle as [q Hq];exists (S q);simpl;rewrite Hq;trivial.
Qed.

Lemma Le_le : forall n p, Le n p -> n <= p.
Proof.
 intros n p [q Hq].
 generalize q p Hq.

  clear Hq. 
 
 induction q0
.
 simpl in *;intros;subst n.
 constructor.
 
 simpl;intros. 
 apply le_trans with (q0 + n).
 auto with arith.
subst p0. 
 auto with arith.
Qed.


Lemma LE_n : forall n, LE n n.
induction n;simpl;auto.
Qed.

Lemma LE_S : forall n p, LE n p -> LE n (S p).
induction n.
simpl;auto.
destruct p.
destruct 1.
simpl.
auto.
Qed.

Lemma le_LE : forall n p, n <= p -> LE n p.
Proof.
 induction 1.
 apply LE_n.
 apply LE_S.
 assumption.
Qed.
 
Lemma LE_Le : forall n p, LE n p -> Le n p.
induction n.
intros p;exists p;simpl;auto.
destruct p.
destruct 1.
simpl; intro H.
destruct (IHn _ H) as [q Hq].
exists q;auto.
subst p.
auto with arith.
Qed.
 







Require Import Arith.

Print leb.
Require Import Max.



Lemma leb_le : forall n p, leb n p = true -> n <= p.
Proof.
 induction n;intro p;case p;simpl.
 
 constructor.
 induction n;constructor;auto.
 intro;discriminate.
 SearchPattern (S _ <= S _).
 intros n0 H ;apply le_n_S.
 apply IHn;trivial.
Qed.

Lemma le_leb : forall n p, n <= p -> leb n p = true.
Proof.
 induction n;intro p;case p;simpl;trivial.
 intro H;inversion H.
 intros m H;inversion H.
 subst m;auto.
 apply IHn.
 apply le_trans with (S n);auto.
Qed.

Lemma le_leb_iff : forall n p, n<=p <-> leb n p=true.
Proof.
 intros n p ;split;intro H.
 apply le_leb;auto.
 apply leb_le;auto.
Qed.


Lemma leb_lt : forall n p, leb n p = false -> p < n.
Proof.
 induction n;intro p;case p;simpl.
 intro;discriminate.
 intros;discriminate.
 auto with arith.
SearchPattern (S _ < S _).
 intros;apply lt_n_S;auto.
Qed.

Lemma lt_leb : forall n p, p < n -> leb n p = false.
Proof.
 induction n;destruct p;simpl;auto.
 inversion 1.
 inversion 1.
 intros H;apply IHn.
 Search lt.
 apply lt_S_n.
 assumption.
Qed.

Lemma lt_leb_iff : forall n p, p < n <-> leb n p = false.
Proof.
 intros n p;split;intro H.
 apply lt_leb;auto.
 apply leb_lt;auto.
Qed.


Lemma L: 0 <= 47.
Proof.
 rewrite  le_leb_iff.
 reflexivity.
Qed.

Lemma leb_n_Sn : forall n, leb n (S n) = true.
Proof.
 intro n;rewrite  le_leb.
 trivial.
 repeat constructor.
Qed.

Lemma leb_Sn_n : forall n p, leb  n (n + p)= true.
Proof.
 intros n p;rewrite le_leb. 
 trivial.
 SearchPattern (_ <= _ + _).
 apply le_plus_l;auto.
Qed.

 
Lemma leb_max : forall n p, max n p = if leb n p then p else n.
Proof.
 intros n p;case_eq (leb n p);intro H.
 rewrite <- le_leb_iff in H.
 SearchAbout (?X <= ?Y -> max _ _ = ?Y).
 apply max_r;auto.
 apply max_l.
 rewrite <- lt_leb_iff  in H.
  SearchAbout (?X < ?Y -> ?X <= ?Y).
apply lt_le_weak.
assumption.
Qed.




(** Exercise 3 *)

Require Import List.

Section On_index.
Variable A : Type.
Variable eqAb : A -> A -> bool.

Inductive eqA_spec (a b:A):bool -> Prop :=
eqA_eq : forall Heq :a = b, eqA_spec a b true
|eqA_diff : forall Hdiff: a <> b , eqA_spec a b false.

Hypothesis eqAbP : forall a b, eqA_spec a b (eqAb a b).


Inductive is_nth (a:A) : nat -> list A -> Prop :=
| is_nth_0 : forall l, is_nth a 0 (a::l)
| is_nth_S : forall p b l, is_nth a p l -> is_nth a (S p) (b::l).


Inductive index_spec (a:A)(l:list A):(option nat)->Prop :=
| success : forall i (Hsuccess:is_nth a i l), index_spec a l (Some i)
| failure : forall (Hfail : forall i, ~ is_nth a i l), index_spec a l None.

Definition index_ok (idx : A -> list A -> option  nat) :=
  forall a l, index_spec a l (idx a l).


  

Fixpoint index (a:A)(l:list A) : option  nat :=
  match l with nil => None
             | b::l' => if eqAb a b then Some 0
                        else match index a l' with  Some i => Some (S i)
                                                 |  None => None
                                              end
  end.


Lemma index_correct : index_ok index.
red;
induction l.
simpl.
constructor.
intros i Hi;inversion Hi.
simpl. 
case_eq (eqAb a a0).
intro e;destruct (eqAbP a a0).
subst a;constructor.
constructor.
discriminate.
case (IHl).
constructor.

constructor.
auto.


constructor.
clear IHl.


intros i Hi.

inversion Hi.
subst a0.
destruct (eqAbP a a).
discriminate.
destruct Hdiff;trivial.

destruct (Hfail p);auto.
Qed.


Lemma index_is_nth: forall a l i, index a l = Some i -> is_nth a i l.
intros a l i;destruct  (index_correct a l).
injection 1. intro;subst i0;auto.
discriminate.
Qed.

Lemma is_nth_index: forall a l i, is_nth a i l -> exists j, index a l = Some j.
intros.
destruct  (index_correct a l).
exists i0;auto.
destruct (Hfail i).
auto.
Qed.



End On_index.

(* Exercise 4 : borrowed and adapted from B. Pierce course "Software Foundations"*)

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
Proof.
intros t1 t1' t2 h12; revert t2.
induction h12; intros t3; simpl.

constructor.
constructor.

constructor.
trivial.

constructor.
constructor.
trivial.
Qed.

(* Prove that evaluation is deterministic: *)
Lemma eval_det : forall t n1 n2, eval t n1 -> eval t n2 -> n1 = n2.
Proof.
intros t n1 n2 h1 h2.
revert n2 h2.
induction h1.
  intros n2; simpl.
  inversion 1.
  trivial.
intros n3 h3.
inversion_clear h3.
rewrite (IHh1_1 n0 H).
rewrite (IHh1_2 n4 H0).
trivial.
Qed.

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
Proof.
  intros t t1 t2 Ht1 Ht2.
  revert t2 Ht2.
  induction Ht1.
  intros t3 ht3.
  inversion ht3.
     reflexivity.

     inversion H2.

     inversion H2.
 
  intros t3 Ht3.
  inversion Ht3.
    rewrite <- H0 in Ht1.
    inversion Ht1.

    rewrite <- (IHHt1 t1'0); trivial.

    rewrite <- H in Ht1.
    inversion Ht1.
 
  intros t3 Ht3.
  inversion Ht3.
    rewrite <- H1 in Ht1.
    inversion Ht1.

    inversion H2.

    rewrite <- (IHHt1 t2'0); trivial.
Qed.



 
 


 

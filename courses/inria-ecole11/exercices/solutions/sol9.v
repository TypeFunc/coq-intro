Require Import List.
Require Import ZArith.
Require Import Arith.

Fixpoint count x l :=
 match l with
 | nil => 0
 | a::l => (if beq_nat x a then 1 else 0) + count x l
 end.

Fixpoint merge (l1 l2:list nat) : list nat :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | x1::l1', x2::l2' =>
    if leb x1 x2 then 
      x1::merge l1' l2
    else 
      x2:: (fix merge_aux (l2:list nat) := 
             match l2 with
             | nil => l1
             | x2::l2' => 
               if leb x1 x2 then 
                  x1::merge l1' l2
               else 
                  x2:: merge_aux l2'
             end) l2'
   end.

Definition permut l1 l2 := forall x, count x l1 = count x l2.

Lemma count_app : forall x l1 l2, count x (l1 ++ l2) = count x l1 + count x l2.
Proof.
 induction l1;simpl;auto.
 intros l2;rewrite IHl1;ring.
Qed.

Lemma merge_perm: forall l1 l2, permut (merge l1 l2) (l1 ++ l2).
Proof.
 unfold permut;intros l1 l2 x;rewrite count_app.
 revert l2;induction l1 as [ | x1 l1 IHl1];[auto | ].
 intros [ | x2 l2];[auto | simpl].
 destruct (leb x1 x2).
 simpl; rewrite IHl1;simpl;ring.
 simpl; ring_simplify.
 rewrite <- !plus_assoc.
 f_equal.
 induction l2;simpl;auto.
 destruct (leb x1 a).
 simpl;rewrite IHl1;simpl;ring.
 simpl;rewrite IHl2;simpl;ring.
Qed.

Section MergeAux.
  Variable merge' : list nat -> list nat -> list nat.
  Variable x1:nat.
  Variable l1':list nat.

  Fixpoint merge_aux l2 :=
    match l2 with
    | nil => x1::l1'
    | x2::l2' => 
      if leb x1 x2 then 
         x1::merge' l1' l2
      else 
         x2:: merge_aux l2'
    end.

  Hypothesis merge_count : forall x l2, 
     count x (merge' l1' l2) = count x l1' + count x l2.

  Lemma merge_aux_count : forall x l2,
     count x (merge_aux l2) = 
       (if beq_nat x x1 then 1 else 0) + count x l1' + count x l2.
  Proof.
   induction l2 as [ | x2 l2' IHl2];simpl;auto.
   destruct (leb x1 x2);simpl.
   rewrite merge_count;simpl;ring.
   rewrite IHl2;ring.
  Qed.

End MergeAux.

Check merge_aux.

Check merge_aux_count.

Fixpoint merge' (l1 l2:list nat) :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | x1::l1', x2::l2' =>
    if leb x1 x2 then 
      x1::merge' l1' l2
    else 
      x2::merge_aux merge' x1 l1' l2'
  end.

Lemma merge'_perm : forall l1 l2, permut (merge' l1 l2) (l1 ++ l2).
Proof.
 unfold permut;intros l1 l2 x;rewrite count_app.
 revert l2 x;induction l1 as [ | x1 l1 IHl1];[auto | ].
 intros [ | x2 l2] x;[auto | simpl].
 destruct (leb x1 x2);simpl.
 rewrite IHl1;simpl;ring.
 rewrite merge_aux_count;[ring | auto].
Qed.

Fixpoint merge'' l1 l2 :=
  let fix merge_aux l2 :=
   match l1, l2 with
   | nil, _ => l2
   | _, nil => l1
   | x1::l1', x2::l2' =>
     if leb x1 x2 then x1::merge'' l1' l2
    else x2::merge_aux l2'
    end 
  in merge_aux l2.

Lemma merge''_perm : forall l1 l2, permut (merge'' l1 l2) (l1 ++ l2).
Proof.
 unfold permut;intros l1 l2 x;rewrite count_app.
 revert l2;induction l1 as [ | x1 l1 IHl1].
 destruct l2;auto.
 induction l2 as [ | x2 l2 IHl2];[auto | ].
 simpl;destruct (leb x1 x2).
 simpl;rewrite IHl1;simpl;ring.
 simpl in IHl2.
 simpl;rewrite IHl2;ring.
Qed.

Definition slen (p:list nat * list nat) :=
  length (fst p) + length (snd p).

(* Complete the definition *)

Require Import Recdef.
Function Merge (p:list nat * list nat) { measure slen p } : list nat :=
  match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | ((x1::l1') as l1, (x2::l2') as l2) =>
     if leb x1 x2 then x1::Merge (l1',l2)
     else x2::Merge (l1,l2')
   end.
(* first goal *)
unfold slen;simpl;intros. omega. 
(* second goal *)
unfold slen;simpl;intros. omega.
Defined.

Compute Merge (2::3::5::7::nil, 3::4::10::nil).

Lemma Merge_count : forall x l1 l2, 
  count x (Merge (l1, l2)) = count x l1 + count x l2.
Proof.
 (* intros x l1 l2;functional induction (Merge (l1,l2)). *)
 (* Some information is lost, we need generalization *)
 intros x l1 l2.
 change l1 with (fst(l1,l2)) at 2.
 change l2 with (snd(l1,l2)) at 3.
 functional induction (Merge (l1,l2));auto.
 simpl;rewrite IHl;simpl;ring.
 simpl;rewrite IHl;simpl;ring.
Qed.


(** Well founded relation *)

Lemma wf_lt : well_founded lt.
Proof.
 unfold well_founded.
 induction a as [ | n IHn].
 constructor;intros y Hlt;elimtype False;omega.
 constructor;intros y Hlt.
 elimtype (y < n \/ y = n).
  destruct IHn;auto.
  intros Heq;rewrite Heq;trivial.
 omega.
Qed.

(* Try to understand what represent the 
   following inductive types and fixpoint *)

Inductive btree : Type :=
| BLeaf : btree 
| BNode : btree -> btree -> btree.

Fixpoint bleft t :=
  match t with
  | BLeaf => t
  | BNode tl tr => bleft tl
  end.

Inductive ntree : Type :=
| NLeaf : ntree
| NNode : list ntree -> ntree.

Inductive itree : Type :=
| ILeaf : itree
| INode : (nat -> itree) -> itree.

Fixpoint ileft t :=
 match t with
 | ILeaf => t
 | INode f => ileft (f 0)
 end.

Inductive dtree : nat -> Type :=
| DNode : forall n, (forall m, m < n -> dtree m) -> dtree n.

(* Remark that there is no constructor DLeaf (the empty tree),
   the following is a representation of the empty tree 
*)

Definition DLeaf : dtree 0.
 constructor.
 intros.
 elimtype False.
 apply (lt_n_O m H).
Defined.

Print DLeaf.

Inductive atree (R:nat->nat->Prop) : nat -> Type :=
| ANode : forall n, (forall m, R m n -> atree R m) -> atree R n.

(* Did you see the relation with Acc *)
Print Acc.

(** Make your own induction principle, use the tactic "fix" *)

Inductive tree (A:Type) :=
 | Node : A -> list (tree A) -> tree A.

Lemma my_tree_ind : forall (A : Type) 
  (P : tree A -> Prop) (Pl : list (tree A) -> Prop),
  (forall a l, Pl l -> P (Node _ a l)) ->
  Pl nil ->
  (forall t l, P t -> Pl l -> Pl (t :: l)) ->
  forall t, P t.
Proof.
 intros A P Pl Hnode Hnil Hcons.
 fix my_tree_ind 1.  
 destruct t as [a l].
 apply Hnode.
 induction l as [ | t l IHl].
 apply Hnil.
 apply Hcons.
 apply my_tree_ind.
 apply IHl.
Qed.

Print my_tree_ind.

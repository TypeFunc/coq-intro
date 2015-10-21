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

(* Complete all the proofs *)
Lemma count_app : forall x l1 l2, count x (l1 ++ l2) = count x l1 + count x l2.
Proof.
Admitted.

Lemma merge_perm: forall l1 l2, permut (merge l1 l2) (l1 ++ l2).
Proof.
Admitted.

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
  Admitted.

End MergeAux.

(* Check the type of merge_aux and merge_aux_count *)
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
Admitted.

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
Admitted.

(** Using Function *)

Require Import Recdef.

Definition slen (p:list nat * list nat) :=
  length (fst p) + length (snd p).

(* Complete the definition *)
Function Merge (p:list nat * list nat) { measure slen p } : list nat :=
  match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | ((x1::l1') as l1, (x2::l2') as l2) =>
     if leb x1 x2 then x1::Merge (l1',l2)
     else x2::Merge (l1,l2')
   end.
(* first goal *)

(* second goal *)

Admitted. (* Defined. (do not use Qed here) *)


Compute Merge (2::3::5::7::nil, 3::4::10::nil).

Lemma Merge_count : forall x l1 l2, 
  count x (Merge (l1, l2)) = count x l1 + count x l2.
Proof.
Admitted.

(** Well founded relation *)

Lemma wf_lt : well_founded lt.
Proof.
Admitted.

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
Admitted.

Print my_tree_ind.

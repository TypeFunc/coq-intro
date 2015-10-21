Require Import List.

Fixpoint fact n :=
    match n with
    | O => 1
    | S n' => n * fact n'
    end.

Definition fact' :=
    fix fact1 n :=
      match n with
      | O => 1
      | S n' => n * fact1 n'
      end.

Fixpoint div2 n :=
  match n with
  | S (S n') => S (div2 n')
  | _ => 0
  end.

Definition pred n := 
  match n with
  | O => n 
  | S n' => n' 
  end.

Fixpoint div2' n :=
  match n with
  | S n' => S (div2' (pred n'))
  | _ => 0
  end.

Fixpoint even n :=
  match n with
  | O => true
  | S n' => odd n'
  end
with odd n :=
  match n with
  | O => false
  | S n' => even n'
  end.

Require Import Arith.

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

Section MergeAux.
  Variable merge : list nat -> list nat -> list nat.
  Variable x1:nat.
  Variable l1':list nat.

  Fixpoint merge_aux l2 :=
    match l2 with
    | nil => x1::l1'
    | x2::l2' => 
      if leb x1 x2 then 
         x1::merge l1' l2
      else 
         x2:: merge_aux l2'
    end.

End MergeAux.
Print merge_aux.

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

Compute merge (2::3::5::7::nil) (3::4::10::nil).
Require Import ZArith.
Open Scope Z_scope.
Require Import Recdef.

Function factZ (x : Z) {measure Zabs_nat x} : Z :=
  if Zle_bool x 0 then 1 else x * factZ (x - 1).
intros x tst.
Check Zle_cases.
assert (cmp := Zle_cases x 0). rewrite tst in cmp.
SearchPattern (Zabs_nat _ < Zabs_nat _)%nat.
apply Zabs_nat_lt. omega.
Defined.
Compute factZ 10.

Open Scope nat_scope.
Definition slen (p:list nat * list nat) :=
  length (fst p) + length (snd p).

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

Open Scope Z_scope.

Require Import Zwf.

Function log10 (n : Z){wf (Zwf 1) n} : Z := 
  if Zlt_bool n 10 then 0 else 1 + log10 (n / 10).
Proof.
  (* first goal *) 
  intros n Hleb.
  unfold Zwf.
  generalize (Zlt_cases n 10) (Z_div_lt n 10);rewrite Hleb.
  omega.
  (* Second goal *)
  apply Zwf_well_founded. 
Defined.
(* Compute log10 2. : you can wait for a answer ... *)

Function log10' (n : Z){measure Zabs_nat n} : Z := 
  if Zlt_bool n 10 then 0 else 1 + log10' (n / 10).
Proof.
  (* first goal *) 
  intros n Hleb.
  unfold Zwf;generalize (Zlt_cases n 10); rewrite Hleb;intros Hle.
  apply Zabs_nat_lt. 
  split.
  apply Z_div_pos;omega.
  apply Zdiv_lt_upper_bound;omega.
Defined.
Compute log10' 100.
Print log10'.
Print log10'_terminate.

(* Proving Properties *)
Open Scope nat_scope.

Lemma div2_le : forall n, div2 n <= n.
Proof.
 induction n.
 auto.
 simpl. 
 destruct n.
 auto.
 (* Does not work: bad induction hypothesis *)
Abort.

Lemma div2_le : forall n, div2 n <= n.
Proof.
 assert (forall m n, n <= m -> div2 n <= n).
  induction m.
   intros n Hle.
   assert (Heq : n = 0) by omega.
   rewrite Heq;auto.
  intros [ | [ | n]]. (* perform the same pattern matching than div2 *)
  auto.
  auto.
  simpl. 
  assert (Hrec := IHm n);omega.
 intros n;eauto.
Qed.

Functional Scheme div2_ind := Induction for div2 Sort Prop.

Lemma div2_le' : forall x, div2 x * 2 <= x.
intros x; functional induction div2 x.
auto.
auto.
omega.
Qed.

Lemma div2_le'' : forall x, div2 x * 2 <= x.
Proof.
intros x; functional induction div2 x; auto with zarith.
Qed.

Lemma even_odd_ok : forall n, 
  (even n = true -> exists p, n = 2*p) /\
  (odd n = true -> exists p, n = 2*p + 1).
Proof.
 induction n.
 split;intros Heq.
 exists 0;trivial. 
 discriminate.
 destruct IHn as [even_ok odd_ok];split;intros Heq.
 destruct (odd_ok Heq) as [p Heq1].
 exists (p+1);ring [Heq1].
 destruct (even_ok Heq) as [p Heq1].
 exists p;ring [Heq1].
Qed.

Lemma even_ok_1 : forall n, even n = true -> exists p, n = 2*p.
Proof.
 intros n;destruct (even_odd_ok n);auto.
Qed.

Lemma odd_ok_1 : forall n, odd n = true -> exists p, n = 2*p + 1.
Proof.
 intros n;destruct (even_odd_ok n);auto.
Qed.

Lemma even_ok : forall n, even n = true -> exists p, n = 2*p
with odd_ok : forall n, odd n = true -> exists p, n = 2*p + 1.
Proof.
 intros [ | n'] Heq.
 (* first lemma *)
 exists 0;auto.
 destruct (odd_ok n' Heq) as [p Heq1].
 exists (p+1);ring [Heq1].
 (* second lemma *)
 intros [ | n'] Heq.
 discriminate Heq.
 destruct (even_ok n' Heq) as [p Heq1].
 exists (p);ring [Heq1].
Qed.

Open Scope Z_scope.

Lemma log10_103_2 : log10 103 = 2.
Proof.
 repeat (rewrite log10_equation;simpl).
 trivial.
Qed.

Open Scope nat_scope.

Fixpoint count x l :=
 match l with
 | nil => 0
 | a::l => (if beq_nat x a then 1 else 0) + count x l
 end.

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

Lemma Merge_count' : forall x l1 l2, 
  count x (Merge (l1, l2)) = count x l1 + count x l2.
Proof.
 intros x l1 l2.
 remember (l1,l2) as p.
 revert l1 l2 Heqp.
 functional induction (Merge p); intros L1 L2 Heq;inversion_clear Heq;auto.
 simpl;rewrite (IHl _ _ (refl_equal _));simpl;ring.
 simpl;rewrite (IHl _ _ (refl_equal _));simpl;ring.
Qed.

Inductive tree (A:Type) :=
 | Node : A -> list (tree A) -> tree A.

Check tree_ind.

Section TreeInd.
 Variable A:Type.
 Variable (P:tree A -> Prop).
 Variable (Pl:list (tree A) -> Prop).
 Hypothesis Hnode: forall a l, Pl l -> P (Node A a l).
 Hypothesis Hnil: Pl nil.
 Hypothesis Hcons: forall t l, P t -> Pl l -> Pl (t::l). 
 
 Fixpoint my_tree_ind t : P t:=
   match t with
   | Node a l =>
     Hnode a l 
      ((fix lind l : Pl l:= 
          match l with 
          | nil => Hnil 
          | t'::l'=> Hcons t' l' (my_tree_ind t') (lind l')
          end) l)
    end.
End TreeInd.

Check my_tree_ind.

(*
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

Open Scope nat_scope.

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

Definition DLeaf : dtree 0.
 constructor.
 intros.
 elimtype False.
 apply (lt_n_O m H).
Defined.
Print DLeaf.

Inductive atree (R:nat->nat->Prop) : nat -> Type :=
| ANode : forall n, (forall m, R m n -> atree R m) -> atree R n.
*)

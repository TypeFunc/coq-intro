(* Exercise 1 *)
(**************)

(* Define an inductive type for the months in the gregorian calendar *)
(*(the english civil calendar) *)

(* Define an inductive type for the four seasons *)

(* What is the inductive principle generated in each case ?*)

(* Define a function mapping each month to the season that contains *)
(* most of its days, using pattern matching *)


(* Exercise 2 *)
(**************)

(* Define the boolean functions bool_xor, bool_and, bool_eq of type *)
(*bool -> bool -> bool, and the function bool_not of type bool -> bool *)


(* prove the following theorems:
Lemma bool_xor_not_eq : forall b1 b2 : bool,
  bool_xor b1 b2 = bool_not (bool_eq b1 b2).

Lemma bool_not_and : forall b1 b2 : bool,
  bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2).

Lemma bool_not_not : forall b : bool, bool_not (bool_not b) = b.

Lemma bool_or_not : forall b : bool, 
  bool_or b (bool_not b) = true.

Lemma bool_id_eq : forall b1 b2 : bool, 
  b1 = b2 <-> bool_eq b1 b2 = true.

Lemma bool_not_or : forall b1 b2 : bool,
  bool_not (bool_or b1 b2) = bool_and (bool_not b1) (bool_not b2).

Lemma bool_or_and : forall b1 b2 b3 : bool,
  bool_or (bool_and b1 b3) (bool_and b2 b3) = 
  bool_and (bool_or b1 b2) b3.
*)

(* Exercise 3 *)
(**************)

(* Let us consider again the type color defined in the lecture :*)
Inductive color:Type :=
 | white | black | yellow | cyan | magenta | red | blue | green.

(* let us define the complement of a color *)

Definition compl (c : color) :=
 match c with 
 | white => black 
 | black => white
 | yellow => blue
 | cyan => red
 | magenta => green
 | red => cyan
 | blue => yellow
 | green => magenta
 end.

(*
Prove the following results:

Lemma compl_compl : forall c, compl (compl c)= c.

Lemma compl_injective : forall c c', compl c = compl c' -> c = c'.

Lemma compl_surjective : forall c, exists c', c = compl  c'.
*)


(* Exercise 4 *)
(**************)

(* Define an inductive type formula : Type that represents the *)
(*abstract language of propositional logic without variables: 
L = L /\ L | L \/ L | ~L | L_true | L_false
*)


(* Define a function formula_holds of type (formula -> Prop computing the *)
(* Coq formula corresponding to an element of type formula *)

(* Define  a function isT_formula of type (formula -> bool) computing *)
(* the intended truth value of (f : formula) *)


(* prove that is (idT_formula f) evaluates to true, then its *)
(*corresponding Coq formula holds ie.:

Require Import Bool.
Lemma isT_formula_correct : forall f : formula, 
   isT_formula f = true <-> formula_holds f.
*)

(* Exercise 5 *)
(**************)

(* We use the inductive type defined in the lecture: *)

Inductive natBinTree : Set :=
| Leaf : natBinTree
| Node : nat -> natBinTree -> natBinTree -> natBinTree.

(* Define a function which sums all the values present in the tree.

Define a function is_zero_present : natBinTree -> bool, which tests whether
the value 0 is present or not in the tree.

Prove several simple statements about the fonctions mirror, tree_size
and tree_height seen in the lecture


It is possible to navigate in a binary tree. Given a tree t and
a path like "from the root, go to the left subtree, then 
 go to the right subtree, then go to the left subtree, etc. "

Such a path can be easily represented by a list of directions

Inductive direction : Set := L (* go left *) | R (* go right *).


Define in coq a function get_label that takes a tree and some path,
and returns the label at which one arrives following the path
(if any)

Fixpoint get_label (path : list direction)(t:natBinTree): option nat:=
(* to complete *)



Consider the following function :
*) 
Require Import Arith.
Require Import Bool.

Fixpoint zero_present (t: natBinTree) : bool :=
match t with Leaf => false
           | Node n t1 t2 =>  beq_nat n 0 ||
                              zero_present t1 ||
                              zero_present t2
end.
(* 
Prove that whenever zero_present t = true, then there exists 
some path p such that get_label p t = Some 0

*)


(* Exercise 6 *)
(* Require Import List. *)
(* Define the function 
split : forall A B : Set, list A * B -> (list A) * (list B)

which transforms a list of pairs into a pair of lists
and the function
combine : forall A B : Set, list A * list B -> list (A * B)
which transforms a pair of lists into a list of pairs.

Write and prove a theorem relating the two functions.
*)
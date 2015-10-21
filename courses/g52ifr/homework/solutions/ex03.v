(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 3 (Bool and operations on sets)
    published 17/10/11, deadline 25/10/11, 18:00 electronic submission

    Use
    $ cw submit ex03.v
    on one of the CS servers
    then look for the coursework ??? labelled 'g52cfr coursework 1' 
    and enter the associated code.

    Multiple submissions are allowed, up to the deadline.

    Try to fill in the missing proofs, using only the basic tactics presented
    in the lectures.
    Do not use auto or tauto. Do not use any additional libraries.

**)

Section Ex03.

Require Import Coq.Bool.Bool.

Section AboutBool.

(* 
For the following proposition about bool, either prove them
or prove their negation (i.e. prove ~(...))

ex31 : exists x y : bool. ~(x = y)
ex32 : exists x y z : bool, ~(x = y) /\ ~(y = z) /\ ~(x = z)
ex33 : exists x : bool. negb x = x
ex34 : forall x y : bool, x || y = y || x
ex35 : forall x : bool, exists y : bool, x || y = x && y
ex36 : exists y : bool, forall x : bool, x || y = x && y
*)

Lemma ex31 : exists x : bool , exists y : bool, ~(x = y).
exists true.
exists false.
intro h.
discriminate h.
Qed.

Lemma ex32 : ~(exists x : bool, exists y, exists z : bool, ~(x = y) /\ ~(y = z) /\ ~(x = z)).
intro h.
destruct h as [x h].
destruct h as [y h].
destruct h as [z h].
destruct h as [xy h].
destruct h as [yz xz].
destruct x.
destruct y.
apply xy.
reflexivity.
destruct z.
apply xz.
reflexivity.
apply yz.
reflexivity.
destruct y.
destruct z.
apply yz.
reflexivity.
apply xz.
reflexivity.
apply xy.
reflexivity.
Qed.

Lemma ex33 : ~ (exists x : bool, negb x = x).
intro h.
destruct h as [x h].
destruct x;
discriminate h.
Qed.

Lemma ex34 : forall x y : bool, x || y = y || x.
intros x y.
destruct x;
  destruct y;
    reflexivity.
Qed.

Lemma ex35 : forall x : bool, exists y : bool, x || y = x && y.
intro x.
destruct x.
exists true.
reflexivity.
exists false.
reflexivity.
Qed.

Lemma ex36 : ~ (exists y : bool, forall x : bool, x || y = x && y).
intro h.
destruct h as [y h].
destruct y.
assert (f : false || true = false && true).
apply h.
discriminate f.
assert (f : true || false = true && false).
apply h.
discriminate f.
Qed.

End AboutBool.

Section Implb.

(* Define an operation implb which implements implication
   and show its correctness. *)

Definition implb(a b : bool) : bool :=
  if a then b else true.

Lemma implb_compl : forall a b : bool, 
  (a = true -> b = true) -> implb a b = true.
intros a b.
destruct a.
intro h.
apply h.
reflexivity.
intro h.
reflexivity.
Qed.

Lemma implb_sound : forall a b : bool, 
  implb a b = true -> (a = true -> b = true).
intros a b h ha.
rewrite ha in h.
exact h.
Qed.

Theorem implb_correct : forall a b : bool, 
  (a = true -> b = true) <-> implb a b = true.
intros a b.
split.
apply implb_compl.
apply implb_sound.
Qed.

End Implb.

Section Tictactoe.
Open Scope type_scope.
Implicit Arguments inl [A B].
Implicit Arguments inr [A B].

(** Represent the game of Tic-tac-toe (see wikipedia) 
    using finite sets, products and coproducts.

    In particular define the following sets
    - Piece : the set pof pieces
    - Coord : the set of coordinates
    - Field : the set of contents of a field
    - Board : the set of boards

   Construct the following board as myboard : Board

   XXO
   .O.
   ...

   Define a function mirrorBoard : Board -> Board 
   which mirrors a board along the diagonal, i.e. in the example we would get
   
   ..O
   .OX
   ..X
*)



Inductive Piece : Set :=
  | O : Piece
  | X : Piece.

Inductive Three : Set :=
  | x1 : Three
  | x2 : Three
  | x3 : Three.

Definition Coord : Set := Three * Three.

Inductive Empty : Set :=
  | empty : Empty.

Definition Field : Set := Piece + Empty.
Definition FX : Field := inl X.
Definition FO : Field := inl O.

Definition emptyField : Field := inr empty.

Definition Board : Set := Coord -> Field.

Definition myBoard : Board :=
  fun xy => match xy with
            | (x , y) => match y with
                           | x1 => emptyField
                           | x2 => match x with
                                   | x1 => emptyField
                                   | x2 => FO
                                   | x3 => emptyField
                                   end
                           | x3 => match x with
                                   | x1 => FX
                                   | x2 => FX
                                   | x3 => FO
                                   end
                         end
            end.

Definition mirrorBoard : Board -> Board :=
  fun board => fun xy => match xy with
                         | (x , y) => board (y , x) 
                         end.

End Tictactoe.

Section Surprise.
(* Prove the following (surprising ?) theorem:

   Given any function f : bool -> bool, applying the function
   three times is the same as applying it once.

   Hint: It is useful to use the tactic case_eq,
   see the reference manual for details.
*)

Lemma tricky : 
  forall (f:bool -> bool) (b:bool), f( f( f( b))) = f b.
intros f b.
destruct b.
case_eq (f true).
intros ftt.
rewrite ftt.
exact ftt.
intro ftf.
case_eq (f false).
intro fft.
exact ftf.
intros fff.
exact fff.
case_eq (f false).
intro fft.
case_eq (f true).
intro ftt.
exact ftt.
intro ftf.
exact fft.
intro fff.
rewrite fff.
exact fff.
Qed.

End Surprise.

End Ex03.
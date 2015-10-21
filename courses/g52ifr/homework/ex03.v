(** Introduction to Formal Reasoning (G52IFR)
    Thorsten Altenkirch

    Exercise 3 (Bool and operations on sets)
    published 31/10/11, deadline 8/11/11, 18:00 electronic submission

    Use
    $ cw submit ex03.v
    on one of the CS servers
    then look for the coursework 417 labelled 'g52cfr coursework 3' 
    and enter the associated code.

    Multiple submissions are allowed, up to the deadline.

    Try to fill in the missing proofs, using only the basic tactics presented
    in the lectures.
    Do not use any additional libraries.

**)

Section Ex04.

Require Import Coq.Bool.Bool.

(** 1 **)

Section AboutBool.

(* 
For the following proposition about bool, either prove them
or prove their negation (i.e. prove ~(...))

Lemma ex31 : exists x : bool, exists y : bool, ~(x = y).
Lemma ex32 : exists x : bool, exists y : bool, exists z : bool, ~(x = y) /\ ~(y = z) /\ ~(x = z).
Lemma ex33 : exists x : bool, negb x = x.
Lemma ex34 : forall x y : bool, x || y = y || x.
Lemma ex35 : forall x : bool, exists y : bool, x || y = x && y.
Lemma ex36 : exists y : bool, forall x : bool, x || y = x && y.
*)




End AboutBool.

(** 2 **)

Section Implb.

(* Define an operation implb which implements implication
   and show its correctness. *)

Definition implb(a b : bool) : bool := 
 
(* Hint: It may be a good idea to prove the two directions
         separately.
*)
Theorem implb_correct : forall a b : bool, 
  (a = true -> b = true) <-> implb a b = true.

End Implb.

(** 3 **)
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

End Tictactoe.

(** 4 **)

Section Surprise.
(* Prove the following (surprising ?) theorem:

   Given any function f : bool -> bool, applying the function
   three times is the same as applying it once.

   Hint: It is useful to use the tactic case_eq,
   see the reference manual for details.
*)

Lemma tricky : 
  forall (f:bool -> bool) (b:bool), f( f( f( b))) = f b.





End Surprise.

End Ex03.
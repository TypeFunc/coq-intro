
Require Import ZArith.
Require Import List.
Open Scope Z_scope.

(* 1 : Give a definition in Coq of the following predicates.

  Unless specifieed, the numbers are supposed to be of type Z , and the
  lists of type "list Z".

  For lists, you could use basic functions on lists such as
  "length", "rev", "nth", ... Be careful with the additional argument
  of nth, providing a default value. *)

(* 1a) the number b is a divisor of a *)

(* 1b) the number n is prime *)

(* 1c) d is the least prime divisor of n *)

(* 1d) the square root of n is rational *)

(* 1e) the list l is palindromic. *)

(* 1f) the list l is sorted. *)

(* 1g) the list l represents the decomposition of n into prime factors *)

(* 2 : Translate into Coq the following statements.
       If some statement is incomplete or ambiguous, please make it
       more precise : *)

(* 2a) Every integer has a unique decomposition into prime factors *)

(* 2bc) The goldbach conjecture : every even number >= 4 could be written
       as a sum of two prime numbers. *)

(* 2d) if a list is sorted and palindromic, then it is a repetition of
       the same number *)

(* 3  Specify any function which takes a list of integers and returns
      a list with the same elements but without duplicates *)

(* 4 The syracuse sequence *)

(*   We consider the following fonction :
     Step(x) = x/2 when x is even
             = 3x+1 when x is odd *)

(* 4a) We won't encode this function in Coq yet. Instead,
       write a relation SyracuseStep : nat -> nat -> Prop, such that
       (SyracuseStep x y) states that y is the half of x when x is even,
       or y is 3x+1 when x is odd. *)

(* 4b) Write a predicate SyracuseSequence : (nat->nat) -> Prop, such that
       (SyracuseSequence f) states that the function f enumerates the iterates
       of the function Step, i.e. f 1 = Step (f 0), etc. *)

(* 4c) Write a Coq statement corresponding to the Syracuse conjecture:
       starting from any strictly positive number, the iteration of the
       Step function will eventually reach 1. *)

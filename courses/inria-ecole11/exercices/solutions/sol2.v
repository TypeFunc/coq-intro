
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

Definition divides b a := exists c, a = b*c.

(* 1b) the number n is prime *)

Definition is_prime (n:Z) :=
  2 <= n /\
  forall p q, 0 < p -> 0 < q -> n = p * q -> p = n \/ q = n.

(* 1c) d is the least prime divisor of n *)

Definition least_prime_divisor d n :=
 is_prime d /\ divides d n /\
 (forall d', is_prime d' -> divides d' n -> d<=d').

(* 1d) the square root of n is rational *)

Definition rational_sqrt n :=
 exists p, exists q, q<>0 /\ q*q*n = p*p.

(* 1e) the list l is palindromic. *)

Definition palindromic_v1 (l:list Z) := (l = rev l).

Definition palindromic_v2 (l:list Z) :=
 forall (i j : nat),
   (1 + i + j = length l)%nat ->
   nth i l 0 = nth j l 0.

(* cf. later a solution based on inductive predicates *)

(* 1f) the list l is sorted. *)

Definition sorted_v1 (l:list Z) :=
 forall l1 l2 x y, l = l1 ++ x::y::l2 -> x<=y.

Fixpoint sorted_v2 (l:list Z) :=
  match l with
    | x::((y::_) as l') => x<=y /\ sorted_v2 l'
    | _ => True
  end.

Definition less_than_all x (l:list Z) := forall y, In y l -> x<=y.
Fixpoint sorted_v3 (l:list Z) :=
  match l with
   | nil => True
   | x::l' => less_than_all x l /\ sorted_v3 l'
  end.

Definition sorted_v4 (l:list Z) :=
 forall (i j:nat), (i<=j<length l)%nat -> nth i l 0 <= nth j l 0.

(* cf. later a solution based on inductive predicates *)


(* 1g) the list l represents the decomposition of n into prime factors *)

Fixpoint prime_decomp_v1 n l :=
  match l with
    | nil => n = 1
    | p::l' => is_prime p /\ exists n', prime_decomp_v1 n' l' /\ n = p*n'
  end.

Fixpoint product l :=
  match l with
    | nil => 1
    | p::l' => p * product l'
  end.

Definition prime_decomp_v2 n l :=
  n = product l /\ (forall p, In p l -> is_prime p).


(* 2 : Translate into Coq the following statements.
       If some statement is incomplete or ambiguous, please make it
       more precise : *)

(* 2a) Every integer has a unique decomposition into prime factors *)

(* We choose to state both existence and unicity (up to permutation).
   We also restrict to integers > 0, in order for our statement to be true *)

  Definition exist_unique_prime_decomp :=
   forall n, 0 < n ->
     exists l, prime_decomp_v2 n l /\
     (forall l l', prime_decomp_v2 n l -> prime_decomp_v2 n l' ->
       sorted_v1 l -> sorted_v1 l' -> l=l').

(* 2bc) The goldbach conjecture : every even number >= 4 could be written
       as a sum of two prime numbers. *)

  Definition goldbach :=
    forall n, 2<=n ->
      exists p, exists q, is_prime p /\ is_prime q /\ 2*n = p+q.

(* 2d) if a list is sorted and palindromic, then it is a repetition of
       the same number *)

  Definition sorted_palindrom_constant :=
    forall l, sorted_v1 l -> palindromic_v1 l ->
      forall x y, In x l -> In y l -> x=y.


(* 3  Specify any function which takes a list of integers and returns
      a list with the same elements but without duplicates *)

  Definition NoDuplicate l :=
    forall i j, (i<j<length l)%nat -> nth i l 0 <> nth j l 0.
  Definition DeduplicateSpec (f:list Z -> list Z) :=
   forall l,
    (forall x, In x l <-> In x (f l)) /\
    NoDuplicate (f l).

(* 4 The syracuse sequence *)

(*   We consider the following fonction :
     Step(x) = x/2 when x is even
             = 3x+1 when x is odd *)

(* 4a) We won't encode this function in Coq yet. Instead,
       write a relation SyracuseStep : nat -> nat -> Prop, such that
       (SyracuseStep x y) states that y is the half of x when x is even,
       or y is 3x+1 when x is odd. *)

Open Scope nat_scope.

Definition SyracuseStep (x y : nat) :=
 forall p, (x = 2*p -> y = p) /\ (x = 2*p+1 -> y = 3*x+1).

(* 4b) Write a predicate SyracuseSequence : (nat->nat) -> Prop, such that
       (SyracuseSequence f) states that the function f enumerates the iterates
       of the function Step, i.e. f 1 = Step (f 0), etc. *)

Definition SyracuseSequence f :=
 forall n, SyracuseStep (f n) (f (S n)).

(* 4c) Write a Coq statement corresponding to the Syracuse conjecture:
       starting from any strictly positive number, the iteration of the
       Step function will eventually reach 1. *)

Definition SyracuseConjecture :=
  forall f, 0 < f 0 -> SyracuseSequence f -> exists n, f n = 1.

(* A proof, anybody ? *)
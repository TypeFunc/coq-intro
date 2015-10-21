Require Import Arith.

(* EXAMPLES *) 
(* The following function takes two arguments a and b
which are numbers of type nat and returns b + 2 * (a + b) *)
Definition f_ex (a b : nat) := b + 2 * (a + b).

(* When p is a pair, you can access its components by the "pattern-matching"
  construct illustrated in the following function. *)
Definition add_pair_components (p : nat * nat) :=
  match p with (a, b) => a + b end.

(* f_ex is a function with two arguments.  add_pair_components is a
  function with one argument, which is a pair. *)

(* 1/ Define a function that takes two numbers as arguments and returns
  the sum of the squares of these numbers. *)

(* 2/ Define a function that takes 5 arguments a b c d e, which are all
   numbers and returns the sum of all these numbers. *)

(* 3/ Define a function named add5 that takes a number as argument and returns
   this number plus 5. *)

(* The following should return 8 *)
Compute add5 3.

(* The following commands make it possible to find pre-defined functions *)
Search nat.
Search bool.

(* 4/ Observe the behavior of the functions Div2.double, Div2.div2, and leb ,
   using "Compute".
   Can you use these three functions to define a function even : nat -> bool
   which returns true exactly when its argument is even? *)

(* 5/ Define a function that takes two arguments.  the first argument
   is a function f of type (nat * nat) -> (nat * nat), the second argument
   a pair of numbers p.  The result should be the pair of numbers obtained
   by apply f to the result of applying f on p.   Call this function iter2p
*)

(* If you defined iter2p correctly, the following test should return
  (1, 2, (2, 3))   
*)
Compute
   (iter2p (fun p => (snd p, fst p)) (1, 2),
    iter2p (fun p => (fst p + 1, snd p + fst p + 1)) (0,0)).

(* 6/ Define a function that takes two functions from nat to nat, f and g,
   and returns the composition of these two functions. *)

(* 7/ Define a function that takes one argument that is a pair of numbers
   and returns the sum of the squares of these numbers. *)

(* 8/ The "leb" function can be used to compare two natural numbers.
   Use it to define a function sm that takes two numbers
   a and b as arguments and returns a + 1 if a is larger than or equal to b
   and b otherwise. Use an if ... then ... else ... construct. *)

(* The following should return 5. *)
Compute sm 4 4.

(* The following should return 6. *)
Compute sm 4 6.

(* 9/ Define a function that takes as input a pair of naturel numbers (a, b)
  and returns as output a pair where the first component is a + 1, and the
  second component is unchanged. *)

(* 10/ Define a function that takes as input a pair of natural numbers (a, b)
   and returns as output a pair where the first component is a +1 and the
   second component is the product of (a + 1) and b *)

(* 11/ Define a function that takes as input a function f of type 
   (nat -> nat -> nat) and a pair of natural numbers (a,b)  and returns
   as output the pair (a+1, f a b) *)

(* 12/ Define a function that takes as input a function g of type
    (nat -> nat), a function f of type (nat -> nat -> nat) and a pair of
    natural numbers (a,b) and returns the pair (g a, f a b) *)

(* DIFFICULT EXERCISE! DIFFICULT EXERCISE (TO BE DONE AT HOME WHEN TIME 
   IS AVAILABLE. *)
(* The following definition describe a computation of the pair
   (8, 8!), where 8! = 1 * 2 * ... * 7 * 8 *)
Definition computation1 :=
  (fun f h p => f (f (f h)) p)
    (fun g p => g (g p))
    (fun p => match p with (x, y) => (x+1, (x+1) * y) end)
    (0, 1).
  
Compute computation1.

(* A/ Some part of computation1 can be replaced by iter2p, 
  do the replacement. Name the new value computation2 and copy it here. *)

Compute computation2.

(* B/ Can you modify computation1 so that it computes (8, 1 + 2 + .. + 8)
   give the name computation3 to your new definition and copy it here. *)

(* The result to the following command should be (8, 36) *)
Compute computation3.
(* D/ f occurs 3 times in (f (f (f h))) and g occurs 2 times in (g (g p)),
   how does this relate to the number 8?
   Can you modify computation1 so that it computes (32, 1 + 2 + .. + 32)?
   Name the result computation4 and copy it here. *)

(*  (the result should be (32, 528)) *)
Compute computation4.


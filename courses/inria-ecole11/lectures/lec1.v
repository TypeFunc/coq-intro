Require Import Arith.

Definition rep2 (f: nat -> nat) (x : nat) := f (f x).
Definition rep2on3 (f: nat -> nat) := rep2 f 3.


Check rep2.
Check rep2on3.
Check add5.
Check rep2 add5.
Check rep2on3 add5.



Definition proj (n: nat) (x: nat -> nat) := x n.

Check proj.

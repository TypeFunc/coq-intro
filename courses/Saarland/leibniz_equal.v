Goal forall (X : Type) (x y : X), (forall p : X -> Prop, p x -> p y) -> x = y.
Proof.
  intros X x y A.
  (** We want to apply A to a predicate p with the following properties:
         p x obviously holds
         p y is x = y.  
      So the predicate we want is the lambda abstraction (fun z -> x = z).
      because then p x is just x = x and p y is x = y.

      A applied to this predicate has type

          ((fun z => x = z) x -> (fun z => x = z) y)

      That is,

          (A (fun z => x = z)) : ((fun z => x = z) x -> (fun z => x = z) y)

      There are two beta reduxes: 
          (fun z => x = z) x, which reduces to x = x
          (fun z => x = z) y, which reduces to x = y

      So A applied to (fun z => x = z) has type (x = x -> x = y), that is,

          (A (fun z => x = z)) : (x = x -> x = y).
      
      Since the type is x=x implies x=y, and since we want to prove x=y,
      we can use the Coq apply tactic to reduce the claim to x=x, which 
      is proved by reflexivity.
   *)
  apply (A (fun z => x = z)).   (* apply the assumption A to the property "being x" *)
  reflexivity.
Qed.

Print Unnamed_thm.
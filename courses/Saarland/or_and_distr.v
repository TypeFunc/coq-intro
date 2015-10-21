Goal forall X Y Z : Prop, X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
Proof.
  intros X Y Z A.
  destruct A as [B | [C D]].
  - split. 
    + left. exact B.
    + left. exact B. 
  - split.
    + right. exact C.
    + right. exact D.
Qed.

Print Unnamed_thm.


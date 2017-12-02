
Theorem Ex033 (A B C : Prop): ((A /\ (B -> C )) -> A) <-> ((A /\ (B -> ~C)) -> A).
Proof.
  split.
  + intros.
    destruct H0.
    exact H0.
  + intros.
    destruct H0.
    exact H0.
Qed.
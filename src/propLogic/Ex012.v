
Theorem Ex012 (A B : Prop): A -> A \/ B.
Proof.
  intro.
  left. exact H.
Qed.
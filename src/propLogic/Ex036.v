
Theorem Ex036 (A B : Prop): (A -> B) -> A -> B.
Proof.
  intros.
  apply H.
  exact H0.
Qed.
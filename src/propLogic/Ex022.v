
Theorem Ex022 (A B C : Prop): (A -> B) -> (A -> B -> C) -> (A -> C).
Proof.
  intros.
  apply H0.
  + exact H1.
  + apply H. exact H1.
Qed.


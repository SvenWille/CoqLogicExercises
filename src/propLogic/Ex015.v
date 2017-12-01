
Theorem Ex015 (A B : Prop): (A -> B) -> A -> A /\ B.
Proof.
  intros.
  split.
  + exact H0.
  + apply H. exact H0.
Qed.

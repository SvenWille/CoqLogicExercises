
Theorem Ex029 (A B C : Prop): (A -> B) -> (C -> ~B) -> (A -> ~C).
Proof.
  intros.
  intro.
  apply H0.
  + exact H2.
  + apply H.
    exact H1.
Qed.
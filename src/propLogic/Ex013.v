
Theorem Ex013 (A B : Prop) :(A -> B) -> (~B -> ~A).
Proof.
  intros.
  intro.
  apply H0. apply H.
  exact H1.
Qed.
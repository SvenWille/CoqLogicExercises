
Theorem Ex043 (A B C : Prop): A /\ B -> ~A \/ C -> ~(A /\ B) -> ~C.
Proof.
  intros.
  intro.
  destruct H.
  apply H1.
  split.
  + exact H.
  + exact H3.
Qed.

Theorem Ex014 (A B : Prop) : A /\ B -> B /\ A.
Proof.
  intro.
  destruct H.
  split.
  + exact H0.
  + exact H.
Qed.


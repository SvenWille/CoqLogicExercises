Require Import Classical.

Theorem Ex027 (A : Prop): A \/ ~A.
Proof.
  apply NNPP.
  intro.
  apply H.
  right.
  intro.
  apply H.
  left.
  exact H0.
Qed.
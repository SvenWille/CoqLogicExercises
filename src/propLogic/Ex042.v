Require Import Classical.

Theorem Ex042 (A : Prop) : (~A -> False) -> A.
Proof.
  intro.
  apply NNPP.
  intro.
  apply H.
  exact H0.
Qed.
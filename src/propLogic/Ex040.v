Require Import Classical.

Theorem Ex040 (A B : Prop): (A -> B) \/ (B -> A).
Proof.
  apply NNPP.
  intro.
  apply H.
  left.
  intro.
  exfalso.
  apply H.
  right.
  intro.
  exact H0.
Qed.
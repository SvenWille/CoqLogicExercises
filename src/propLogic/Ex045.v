Require Import Classical.

Theorem Ex045 (A B C : Prop): C -> ~A \/ ((B \/ C) -> A).
Proof.
  intro.
  apply NNPP.
  intro. 
  apply H0.
  left.
  intro.
  apply H0.
  right.
  intro.
  exact H1.
Qed.
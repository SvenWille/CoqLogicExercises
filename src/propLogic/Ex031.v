Require Import Classical.

Theorem Ex031 (A B C : Prop):  (A -> B) \/ A <-> (B -> A) \/ B.
Proof.
  split.
  + intro.
    destruct H.
    - apply NNPP.
      intro.
      apply H0.
      left.
      intro.
      apply NNPP.
      intro.
      apply H0.
      right.
      exact H1.
    - left.
      intro.
      exact H.
  + intro.
    destruct H.
    - apply NNPP.
      intro.
      apply H0.
      left.
      intro.
      apply NNPP.
      intro.
      apply H0.
      right.
      exact H1.
    - left.
      intro.
      exact H.
Qed.
Require Import Classical.

Theorem Ex008 (A B : Prop): ~(A/\ B) -> ~A \/ ~B.
Proof.
  intros.
  destruct (classic (~A \/ ~B)).
  + exact H0.
  + right.
    destruct (classic (~A)).
    - intro.
      apply H0.
      left.
      exact H1.
    - apply NNPP in H1.
      intro.
      apply H.
      split.
      * exact H1.
      * exact H2.
Qed.
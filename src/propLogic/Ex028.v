Require Import Classical.

Theorem Ex028 (A B : Prop): ~(A /\ B) <-> (~A \/ ~B).
Proof.
  split.
  + intro.
    apply NNPP.
    intro.
    apply H0.
    left.
    intro.
    apply H0.
    right.
    intro.
    apply H.
    split.
    - exact H1.
    - exact H2.
  + intro.
    intro.
    destruct H0.
    destruct H.
    - apply H. exact H0.
    - apply H. exact H1.
Qed.
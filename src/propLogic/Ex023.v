Require Import Classical.

Theorem Ex023 (A B : Prop): (A -> B) <-> (~A \/ B).
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
    apply H.
    exact H1.
  + intros.
    destruct H.
    - contradiction.
    - exact H.
Qed.
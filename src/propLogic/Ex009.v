Require Import Classical.

Theorem Ex009 (a b c : Prop) : ~c -> a \/ ((a \/ c) -> b).
Proof.
  intro.
  apply NNPP.
  intro.
  apply H0.
  right.
  apply NNPP.
  intro.
  apply H1.
  intro.
  destruct H2.
  + exfalso.
    apply H0. left. exact H2.
  + exfalso. apply H. exact H2.
Qed.
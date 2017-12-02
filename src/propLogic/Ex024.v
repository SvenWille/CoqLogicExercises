Require Import Classical.

Theorem Ex024 (A B : Prop): (A <-> B) <-> (~A <-> ~B).
Proof.
  split.
  + intro.
    destruct H.
    split.
    - intro. intro.
      apply H1. apply H0. exact H2.
    - intro. intro. apply H1. apply H. exact H2.
  + intro. 
    destruct H.
    split.
    - intro.
      apply NNPP.
      intro.
      apply H0.
      * exact H2.
      * exact H1.
    - intro. apply NNPP.
      intro. apply H. 
      * exact H2.
      * exact H1.
Qed.
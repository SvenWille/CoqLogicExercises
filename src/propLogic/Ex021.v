Require Import Classical.

Theorem Ex021 (A B : Prop): (A <-> B) <-> (A /\ B) \/ (~A /\ ~B).
Proof.
  split.
  + intro.
    destruct H.
    apply NNPP.
    intro.
    apply H1.
    right. 
    split.
    - intro. 
      apply H1. left. split. 
      * exact H2.
      * apply H. exact H2.
    - intro.
      apply H1. left. split.
      * apply H0. exact H2.
      * exact H2.
  + intro.
    split.
    - intro.
      destruct H.
      * destruct H. exact H1.
      * destruct H. exfalso. apply H. exact H0.
    - intro.
      destruct H.
      * destruct H.
        exact H.
      * destruct H. exfalso. apply H1. exact H0.
Qed.
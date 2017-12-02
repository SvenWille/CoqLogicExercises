Require Import Classical.

Theorem Ex032 (A B C : Prop): ((A /\ B ) -> C) <-> ((A -> C) \/ (~C -> ~B)).
Proof.
  split.
  + intro.
    apply NNPP.
    intro.
    apply H0.
    left.
    intro.
    apply H.
    split.
    - exact H1.
    - apply NNPP.
      intro. 
      apply H0.
      right.
      intro.
      exact H2.
  + intros.
    destruct H0.
    destruct H.
    - apply H.
      exact H0.
    - apply NNPP.
      intro.
      apply H.
      * exact H2.
      * exact H1.
Qed.
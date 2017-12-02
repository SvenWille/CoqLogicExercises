Require Import Classical.

Theorem Ex030 (A B C : Prop) :  (A -> B -> C) <-> (~C -> A -> ~B).
Proof.
  split.
  + intro.
    intros.
    intro.
    apply H0.
    apply H.
    - exact H1.
    - exact H2.
  + intros.
    apply NNPP.
    intro.
    apply H.
    * exact H2.
    * exact H0.
    * exact H1.
Qed.
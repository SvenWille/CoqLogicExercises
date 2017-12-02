Require Import Classical.

Theorem Ex044 (A B C : Prop) :  ~(~(A -> B) /\ ~B) -> (~C -> A) -> C \/ B.
Proof.
  intros.
  apply NNPP.
  intro.
  apply H.
  split.
  + intro.
    apply H1.
    right.
    apply H2.
    apply H0.
    intro.
    apply H1.
    left. exact H3.
  + intro.
    apply H1.
    right. exact H2.
Qed.
Require Import Classical.


Theorem pierce (A B : Prop): ((A -> B) -> A) -> A.
Proof.
  intro.
  destruct (classic A).
  + exact H0.
  + apply H.
    intro.
    contradiction.
Qed.
  
Require Import Classical.

Theorem Ex025 (A : Prop): A <-> ~~A.
Proof.
  split.
  + intro.
    intro.
    contradiction.
  + intro.
    apply NNPP.
    intro. 
    contradiction.
Qed.

(*without NNPP*)

Theorem Ex025_2 (A : Prop): A <-> ~~A.
Proof.
  split.
  + intro.
    intro.
    contradiction.
  + intro.
    pose proof (classic A).
    destruct H0.
    - exact H0.
    - contradiction.
Qed.
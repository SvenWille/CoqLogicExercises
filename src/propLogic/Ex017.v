
Theorem Ex017 (A B C : Prop) : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split.
  + intro.
    destruct H.
    destruct H.
    split.
    - exact H.
    - split.
      * exact H1.
      * exact H0.
  + intro.
    destruct H.
    destruct H0.
    split.
    - split.
      * exact H.
      * exact H0.
    - exact H1.
Qed.
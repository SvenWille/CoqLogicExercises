
Theorem Ex019 (A B C : Prop) :  A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  split.
  + intro.
    destruct H.
    destruct H0.
    - left. split.
      * exact H.
      * exact H0.
    - right. split.
      * exact H.
      * exact H0.
  + intro. destruct H.
    - destruct H. split.
      * exact H.
      * left. exact H0.
    - destruct H. split.
      * exact H.
      * right. exact H0.
Qed.
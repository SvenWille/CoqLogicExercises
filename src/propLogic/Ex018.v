
Theorem Ex018 (A B C: Prop): (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split.
  + intro.
    destruct H.
    - destruct H.
      * left. exact H.
      * right. left. exact H.
    - right. right. exact H.
  + intro. 
    destruct H.
    - left. left. exact H.
    - destruct H.
      * left. right. exact H.
      * right. exact H.
Qed.
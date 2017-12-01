
Theorem Ex020 (A B C : Prop): A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  split.
  + intro.
    split.
    - destruct H.
      * left. exact H.
      * destruct H. right. exact H.
    - destruct H.
      * left. exact H.
      * destruct H. right. exact H0.
  + intro.
    destruct H.
    destruct H.
    - destruct H0.
      * left. exact H.
      * left.  exact H.
    - destruct H0. 
      * left. exact H0.
      * right. split.
        ++ exact H.
        ++ exact H0.
Qed.
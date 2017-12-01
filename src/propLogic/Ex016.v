
Theorem Ex016 (A B : Prop) : A \/ B <-> B \/ A.
Proof.
  split.
  + intro.
    destruct H.
    - right. exact H.
    - left. exact H.
  + intro.
    destruct H.
    - right. exact H.
    - left. exact H.
Qed.
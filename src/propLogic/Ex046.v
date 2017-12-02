
Theorem Ex046 (A B : Prop): (A /\ (A -> ~A)) -> (A /\ (B -> ~A)).
Proof.
  intro.
  destruct H.
  split.
  + exact H.
  + intro. intro.
    apply H0.
    - exact H.
    - exact H.
Qed.
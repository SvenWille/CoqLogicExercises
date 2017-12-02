
Theorem Ex026 (A B C : Prop):  (A -> (B -> C)) <-> (B -> (A -> C)).
Proof.
  split.
  + intros.
    apply H.
    - exact H1.
    - exact H0.
  + intros.
    apply H.
    - exact H1.
    - exact H0.
Qed.
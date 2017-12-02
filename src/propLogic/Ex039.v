
Theorem Ex039 (A B C D : Prop) : ~(((A -> B) /\ A) /\ (B -> ~C /\ ~C -> B)) -> ((~D -> B) \/ (B -> (~B -> ~A))).
Proof.
  intros.
  right.
  intros.
  contradiction.
Qed.
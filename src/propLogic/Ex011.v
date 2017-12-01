
Theorem Ex011 (A B : Prop) : (A /\ ~A) -> B.
Proof.  
  intro.
  destruct H.
  exfalso.
  apply H0.
  exact H.
Qed.

Theorem Ex011_2 (A B : Prop) : (A /\ ~A) -> B.
Proof.
  intro.
  destruct H.
  contradiction.
Qed.
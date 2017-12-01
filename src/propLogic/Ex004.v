

(*Proof (A -> (B /\ C)) -> (A -> B) *)


Theorem Ex004 (A B C : Prop): (A -> (B /\ C)) -> (A -> B).
Proof.
  intros.
  apply H in H0.
  destruct H0.
  exact H0.
Qed.
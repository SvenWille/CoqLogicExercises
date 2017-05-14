
(*Proof A \/ B -> A \/ C -> A \/ (B /\ C)*)


Lemma Ex06 : forall (A B C : Prop), A \/ B -> A \/ C -> A \/ (B /\ C).
Proof.
  intros.
  destruct H.
  left.
  exact H.
  destruct H0.
  left.
  exact H0.
  right.
  split.
  exact H.
  exact H0.
Qed.

(*Proof A \/ B -> A \/ C -> A \/ (B /\ C)*)


Lemma Ex06 {a b c : Prop}: a \/ b -> a \/ c -> a \/ (b /\ c).
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
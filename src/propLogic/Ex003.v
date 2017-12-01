
(*Proof: ~A -> A -> B*)


Theorem Ex003: forall (A B : Prop), ~A -> A -> B.
Proof.
  intros.
  contradiction.
Qed.


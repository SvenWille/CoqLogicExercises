
(*Proof: ~A -> A -> B*)


Lemma Ex03_1 : forall (A B : Prop), ~A -> A -> B .
Proof.
  intros.
  contradiction.
Qed.



(*Proof: ~A -> A -> B*)


Lemma Ex03_1 {a b : Prop}: ~a -> a -> b .
Proof.
  intros.
  contradiction.
Qed.


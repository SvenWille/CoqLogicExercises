
(*Proof: A -> A*)


Theorem Ex001_1 (A : Prop): A -> A.
Proof.
  intros.
  exact H.
Qed.

(*using automation*)

Theorem Ex001_2 (A : Prop): A -> A.
Proof.
  auto.
Qed.


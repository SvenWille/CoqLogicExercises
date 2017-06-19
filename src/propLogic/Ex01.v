
(*Proof: A -> A*)


Lemma Ex01_1 {a : Prop}: a -> a.
Proof.
  intros.
  exact H.
Qed.

(*using automation*)

Lemma Ex01_2 {a : Prop}: a -> a.
Proof.
  auto.
Qed.


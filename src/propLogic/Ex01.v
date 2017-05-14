
(*Proof: A -> A*)


Lemma Ex01_1 : forall A : Prop , A -> A .
Proof.
  intros.
  exact H.
Qed.

(*using automation*)

Lemma Ex01_2 :  forall A : Prop , A -> A .
Proof.
  auto.
Qed.


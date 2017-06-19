
(*Proof: A -> B -> A*)

Lemma Ex02_1 {a b : Prop}: a -> b -> a.
Proof. 
  intros.
  exact H.
Qed.


(*using automation*)

Lemma Ex02_2 {a b : Prop}: a -> b -> a.
Proof.
  firstorder.  (*auto would be enough*)
Qed.
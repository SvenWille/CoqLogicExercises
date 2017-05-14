
(*Proof: A -> B -> A*)

Lemma Ex02_1 : forall (A B : Prop), A -> B -> A.
Proof. 
  intros.
  exact H.
Qed.


(*using automation*)

Lemma Ex02_2 : forall (A B : Prop), A -> B -> A.
Proof.
  firstorder.  (*auto would be enough*)
Qed.
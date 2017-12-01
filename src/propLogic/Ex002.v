
(*Proof: A -> B -> A*)

Theorem Ex002_1 (A B : Prop): A -> B -> A.
Proof. 
  intros.
  exact H.
Qed.


(*using automation*)

Theorem Ex002_2 (A B : Prop): A -> B -> A.
Proof.
  firstorder.  (*auto would be enough*)
Qed.
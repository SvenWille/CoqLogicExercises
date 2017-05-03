

(*Proof (A -> (B /\ C)) -> (A -> B) *)


Lemma Ex04 : forall (A B C : Prop), (A -> (B /\ C)) -> (A -> B).
Proof.
intros.
apply H in H0.
destruct H0.
exact H0.
Qed.
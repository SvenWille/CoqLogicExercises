

(* Proof (A /\ (B -> ~A)) -> (A /\ ~B) *)



Theorem Ex05 (A B : Prop): (A /\ (B -> ~A)) -> (A /\ ~B).
Proof.
  intros.
  destruct H.
  split.
  exact H.
  unfold not.
  intro.
  apply  H0 in H1.
  apply H1.
  exact H.
Qed.
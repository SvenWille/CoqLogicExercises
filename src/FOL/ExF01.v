
(* Proof P a -> Q a -> ex x . P x /\ Q x *)


Lemma ExF01 : forall (P Q : Set -> Prop), forall(a : Prop), P a -> Q a -> exists (x : Prop), P x /\ Q x.
Proof.
  intros.
  exists a.
  split.
  exact H.
  exact H0.
Qed.

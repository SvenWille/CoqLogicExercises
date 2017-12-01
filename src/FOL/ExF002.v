
Theorem ExF002 {X : Type} (P Q : X -> Prop) (a : X): (forall x, P x -> Q x) -> P a -> Q a.
Proof.
  intros.
  specialize (H a).
  apply H.
  exact H0.
Qed.



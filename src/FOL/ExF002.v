


Lemma ExF002 :forall {X : Type}, forall {P Q : X -> Prop}, forall {a : X}, (forall x, P x -> Q x) -> P a -> Q a.
Proof.
  intros.
  specialize (H a).
  apply H.
  exact H0.
Qed.



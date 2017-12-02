
Theorem Ex034 (A B C D : Prop) : (A \/ ((B -> C) /\ D)) -> ((B \/ A) \/ (~C -> D)).
Proof.
  intros.
  destruct H.
  + left. right. exact H.
  + destruct H.
    right. intro. exact H0.
Qed.
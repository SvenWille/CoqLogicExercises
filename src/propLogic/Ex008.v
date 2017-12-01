Require Import Classical.

Lemma Ex008 : forall {a b : Prop}, ~(a/\ b) -> ~a \/ ~b.
Proof.
  intros.
  destruct (classic (~a \/ ~b)).
  exact H0.
  right.
  destruct (classic (~a)).
  intro.
  apply H0.
  left.
  exact H1.
  apply NNPP in H1.
  intro.
  apply H.
  split.
  exact H1.
  exact H2.
Qed.
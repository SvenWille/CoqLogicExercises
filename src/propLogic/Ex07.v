Require Import Classical.


Lemma pierce {a b : Prop}: ((a -> b) -> a) -> a.
Proof.
  intro.
  destruct (classic a).
  exact H0.
  apply H.
  intro.
  contradiction.
Qed.
  
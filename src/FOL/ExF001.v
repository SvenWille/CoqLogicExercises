
(* Proof P a -> Q a -> ex x . P x /\ Q x *)


Theorem ExF001 {X : Type}(P Q : X -> Prop)(a : X): P a -> Q a -> exists (x : X), P x /\ Q x.
Proof.
  intros.
  exists a.
  split.
  + exact H.
  + exact H0.
Qed.

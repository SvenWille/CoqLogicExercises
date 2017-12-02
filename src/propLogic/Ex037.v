
Theorem Ex037 (A B C : Prop) :  A \/ B -> ~A \/ ~C -> C -> B.
Proof.
  intros.
  destruct H.
  + destruct H0. 
    - contradiction.
    - contradiction.
  + exact H.
Qed.




Theorem Ex041 (A B C : Prop) :  B /\ B -> A -> ((C \/ ~B) \/ A <-> A /\ ~(B -> ~A)).
Proof.
  intro.
  destruct H.
  split.
  + intro.
    split.
    - exact H1.
    - intro. apply H3.
      * exact H.
      * exact H1.
  + intro.
    right.
    exact H1.
Qed.
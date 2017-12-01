# LogicExercisesInCoq

- scroll down for exercises in FOL (first order logic)  

## Propositional Logic

Proof the following theorems

**Exercise 1: A -> A**
```Coq
Theorem Ex001_1 (A : Prop): A -> A.
Proof.
  intros.
  exact H.
Qed.
```

**Exercise 2: A -> B -> A**

```coq
Theorem Ex002_1 (A B : Prop): A -> B -> A.
Proof. 
  intros.
  exact H.
Qed.
```


**Exercise 3: ~A -> A -> B**

```coq
Theorem Ex003 (A B : Prop): ~A -> A -> B.
Proof.
  intros.
  contradiction.
Qed.
```

**Exercise 4: (A -> (B /\ C)) -> (A -> B)**
```coq
Theorem Ex004 (A B C : Prop): (A -> (B /\ C)) -> (A -> B).
Proof.
  intros.
  apply H in H0.
  destruct H0.
  exact H0.
Qed.
```

**Exercise 5: (A /\ (B -> ~A)) -> (A /\ ~B)**
```coq
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
```

**Exercise 6: A \\/ B -> A \\/ C -> A \\/ (B /\ C)**

```coq
Theorem Ex06 (A B C : Prop): A \/ B -> A \/ C -> A \/ (B /\ C).
Proof.
  intros.
  destruct H.
  + left.
    exact H.
  + destruct H0.
    - left.
      exact H0.
    - right.
      split.
      * exact H.
      * exact H0.
Qed.
```

**Exercise 7: ((A -> B) -> A) -> A**
```coq
Theorem pierce (A B : Prop): ((A -> B) -> A) -> A.
Proof.
  intro.
  destruct (classic A).
  + exact H0.
  + apply H.
    intro.
    contradiction.
Qed.
```

**Exercise 8: ~(A/\ B) -> ~A \\/ ~B**
```coq
Require Import Classical.

Theorem Ex008 (A B : Prop): ~(A/\ B) -> ~A \/ ~B.
Proof.
  intros.
  destruct (classic (~A \/ ~B)).
  + exact H0.
  + right.
    destruct (classic (~A)).
    - intro.
      apply H0.
      left.
      exact H1.
    - apply NNPP in H1.
      intro.
      apply H.
      split.
      * exact H1.
      * exact H2.
Qed.
```

**Exercise 9: ~C -> A \\/ ((A \\/ C) -> B)**
```coq
Require Import Classical.

Theorem Ex009 (A B C : Prop) : ~C -> A \/ ((A \/ C) -> B).
Proof.
  intro.
  apply NNPP.
  intro.
  apply H0.
  right.
  apply NNPP.
  intro.
  apply H1.
  intro.
  destruct H2.
  + exfalso.
    apply H0. left. exact H2.
  + exfalso. apply H. exact H2.
Qed.
```

**Exercise 10: A \\/ ~False**
```coq
Theorem Ex010 (A : Prop) : A \/ ~False.
Proof.
  right.
  intro.
  exact H.
Qed.
```

**Exercise 11: (A /\ ~A) -> B**
```coq
Theorem Ex011 (A B : Prop) : (A /\ ~A) -> B.
Proof.  
  intro.
  destruct H.
  exfalso.
  apply H0.
  exact H.
Qed.
```

**Exercise 12: A -> A \\/ B**
```coq
Theorem Ex012 (A B : Prop): A -> A \/ B.
Proof.
  intro.
  left. exact H.
Qed.
```

**Exercise 13: (A -> B) -> (~B -> ~A)**
```coq
Theorem Ex013 (A B : Prop) :(A -> B) -> (~B -> ~A).
Proof.
  intros.
  intro.
  apply H0. apply H.
  exact H1.
Qed.
```

**Exercise 14: A /\ B -> B /\ A**
```coq
Theorem Ex014 (A B : Prop) : A /\ B -> B /\ A.
Proof.
  intro.
  destruct H.
  split.
  + exact H0.
  + exact H.
Qed.
```

**Exercise 15: (A -> B) -> A -> A /\ B**
```coq
Theorem Ex015 (A B : Prop): (A -> B) -> A -> A /\ B.
Proof.
  intros.
  split.
  + exact H0.
  + apply H. exact H0.
Qed.
```
## First Order Logic

**Exercise 1: P a -> Q a -> exists (x : Prop), P x /\ Q x**

```coq
Theorem ExF001 {X : Type}(P Q : X -> Prop)(a : X): P a -> Q a -> exists (x : X), P x /\ Q x.
Proof.
  intros.
  exists a.
  split.
  + exact H.
  + exact H0.
Qed.
```

**Exercise 2: (forall x, P x -> Q x) -> P a -> Q a.**
```coq
Theorem ExF002 {X : Type} (P Q : X -> Prop) (a : X): (forall x, P x -> Q x) -> P a -> Q a.
Proof.
  intros.
  specialize (H a).
  apply H.
  exact H0.
Qed.
```

**Exercise 3: (forall x, P x -> P (Q x)) /\ P a -> P (Q (Q a))**
```coq
Theorem ExF003_2 {X :Type} (P : X -> Prop) (Q : X -> X) (a : X): (forall x, P x -> P (Q x)) /\ P a -> P (Q (Q a)).
Proof.
  intros.
  destruct H.
  apply H.
  apply H.
  assumption.
Qed.
```
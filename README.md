# LogicForwardProofs

- scroll down for exercises in FOL (first order logic)  
- for original source code (using plain ascii instead of unicode) and alternative/other solutions have a look at the "src" folder  

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
Theorem Ex003: ~A -> A -> B.
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
## First Order Logic

**Exercise 1: forall (P Q : Set -> Prop), forall(a : Prop), P a -> Q a -> exists (x : Prop), P x /\ Q x**

```coq
Lemma ExF01 : {X : Type}{P Q : X -> Prop}{a : X}: P a -> Q a -> exists (x : X), P x /\ Q x.
Proof.
  intros.
  exists a.
  split.
  exact H.
  exact H0.
Qed.

```

**Exercise 2: forall {X : Type}, forall {P Q : X -> Prop}, forall {a : X}, (forall x, P x -> Q x) -> P a -> Q a.**
```coq
Lemma ExF002 :forall {X : Type}, forall {P Q : X -> Prop}, forall {a : X}, (forall x, P x -> Q x) -> P a -> Q a.
Proof.
  intros.
  specialize (H a).
  apply H.
  exact H0.
Qed.
```
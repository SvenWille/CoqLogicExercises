# LogicForwardProofs

- scroll down for exercises in FOL (first order logic)  
- for original source code (using plain ascii instead of unicode) and alternative/other solutions have a look at the "src" folder  

## Propositional Logic

Proof the following theorems

**Exercise 1: A -> A**
```Coq
Lemma Ex01_1 : forall A : Prop , A -> A .
Proof.
  intros.
  exact H.
Qed.
```

**Exercise 2: A -> B -> A**

```coq
Lemma Ex02_1 : forall (A B : Prop), A -> B -> A.
Proof. 
  intros.
  exact H.
Qed.
```


**Exercise 3: forall (A B : Prop), ~A -> A -> B**

```coq
Lemma Ex03_1 : forall (A B : Prop), ~A -> A -> B .
Proof.
  intros.
  contradiction.
Qed.
```

**Exercise 4: forall (A B C : Prop), (A -> (B /\ C)) -> (A -> B)**
```coq
Lemma Ex04 : forall (A B C : Prop), (A -> (B /\ C)) -> (A -> B).
Proof.
  intros.
  apply H in H0.
  destruct H0.
  exact H0.
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
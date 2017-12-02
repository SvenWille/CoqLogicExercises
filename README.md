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

**Exercise 16: A \\/ B <-> B \\/ A**
```coq
Theorem Ex016 (A B : Prop) : A \/ B <-> B \/ A.
Proof.
  split.
  + intro.
    destruct H.
    - right. exact H.
    - left. exact H.
  + intro.
    destruct H.
    - right. exact H.
    - left. exact H.
Qed.
```

**Exercise 17: (A /\ B) /\ C <-> A /\ (B /\ C)**
```coq
Theorem Ex017 (A B C : Prop) : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split.
  + intro.
    destruct H.
    destruct H.
    split.
    - exact H.
    - split.
      * exact H1.
      * exact H0.
  + intro.
    destruct H.
    destruct H0.
    split.
    - split.
      * exact H.
      * exact H0.
    - exact H1.
Qed.
```

**Exercise 18: (A \\/ B) \\/ C <-> A \\/ (B \\/ C)**
```coq
Theorem Ex018 (A B C: Prop): (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split.
  + intro.
    destruct H.
    - destruct H.
      * left. exact H.
      * right. left. exact H.
    - right. right. exact H.
  + intro. 
    destruct H.
    - left. left. exact H.
    - destruct H.
      * left. right. exact H.
      * right. exact H.
Qed.
```

**Exercise 19: A /\ (B \\/ C) <-> (A /\ B) \\/ (A /\ C)**
```coq
Theorem Ex019 (A B C : Prop) :  A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  split.
  + intro.
    destruct H.
    destruct H0.
    - left. split.
      * exact H.
      * exact H0.
    - right. split.
      * exact H.
      * exact H0.
  + intro. destruct H.
    - destruct H. split.
      * exact H.
      * left. exact H0.
    - destruct H. split.
      * exact H.
      * right. exact H0.
Qed.
```

**Exercise 20: A \\/ (B /\ C) <-> (A \\/ B) /\ (A \\/ C)**
```coq
Theorem Ex020 (A B C : Prop): A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  split.
  + intro.
    split.
    - destruct H.
      * left. exact H.
      * destruct H. right. exact H.
    - destruct H.
      * left. exact H.
      * destruct H. right. exact H0.
  + intro.
    destruct H.
    destruct H.
    - destruct H0.
      * left. exact H.
      * left.  exact H.
    - destruct H0. 
      * left. exact H0.
      * right. split.
        ++ exact H.
        ++ exact H0.
Qed.
```

**Exercise 21: (A <-> B) <-> (A /\ B) \/ (~A /\ ~B)**
```coq
Require Import Classical.

Theorem Ex021 (A B : Prop): (A <-> B) <-> (A /\ B) \/ (~A /\ ~B).
Proof.
  split.
  + intro.
    destruct H.
    apply NNPP.
    intro.
    apply H1.
    right. 
    split.
    - intro. 
      apply H1. left. split. 
      * exact H2.
      * apply H. exact H2.
    - intro.
      apply H1. left. split.
      * apply H0. exact H2.
      * exact H2.
  + intro.
    split.
    - intro.
      destruct H.
      * destruct H. exact H1.
      * destruct H. exfalso. apply H. exact H0.
    - intro.
      destruct H.
      * destruct H.
        exact H.
      * destruct H. exfalso. apply H1. exact H0.
Qed.
```

**Exercise 22: (A -> B) -> (A -> B -> C) -> (A -> C)**
```coq
Theorem Ex022 (A B C : Prop): (A -> B) -> (A -> B -> C) -> (A -> C).
Proof.
  intros.
  apply H0.
  + exact H1.
  + apply H. exact H1.
Qed.
```

**Exercise 23: (A -> B) <-> (~A \/ B)**
```coq
Require Import Classical.

Theorem Ex023 (A B : Prop): (A -> B) <-> (~A \/ B).
Proof.
  split.
  + intro.
    apply NNPP.
    intro.
    apply H0.
    left.
    intro.
    apply H0.
    right.
    apply H.
    exact H1.
  + intros.
    destruct H.
    - contradiction.
    - exact H.
Qed.
```

**Exercise 24: (A <-> B) <-> (~A <-> ~B)**
```coq
Require Import Classical.

Theorem Ex024 (A B : Prop): (A <-> B) <-> (~A <-> ~B).
Proof.
  split.
  + intro.
    destruct H.
    split.
    - intro. intro.
      apply H1. apply H0. exact H2.
    - intro. intro. apply H1. apply H. exact H2.
  + intro. 
    destruct H.
    split.
    - intro.
      apply NNPP.
      intro.
      apply H0.
      * exact H2.
      * exact H1.
    - intro. apply NNPP.
      intro. apply H. 
      * exact H2.
      * exact H1.
Qed.
```

**Exercise 25: A <-> ~~A**
```coq
Require Import Classical.

Theorem Ex025 (A : Prop): A <-> ~~A.
Proof.
  split.
  + intro.
    intro.
    contradiction.
  + intro.
    apply NNPP.
    intro. 
    contradiction.
Qed.

(*without NNPP*)

Theorem Ex025_2 (A : Prop): A <-> ~~A.
Proof.
  split.
  + intro.
    intro.
    contradiction.
  + intro.
    pose proof (classic A).
    destruct H0.
    - exact H0.
    - contradiction.
Qed.
```

**Exercise 26: (A -> (B -> C)) <-> (B -> (A -> C))**
```coq
Theorem Ex026 (A B C : Prop):  (A -> (B -> C)) <-> (B -> (A -> C)).
Proof.
  split.
  + intros.
    apply H.
    - exact H1.
    - exact H0.
  + intros.
    apply H.
    - exact H1.
    - exact H0.
Qed.
```

**Exercise 27: A \\/ ~A**
```coq
Require Import Classical.

Theorem Ex027 (A : Prop): A \/ ~A.
Proof.
  apply NNPP.
  intro.
  apply H.
  right.
  intro.
  apply H.
  left.
  exact H0.
Qed.
```

**Exercise 28: ~(A /\ B) <-> (~A \\/ ~B)**
```coq
Require Import Classical.

Theorem Ex028 (A B : Prop): ~(A /\ B) <-> (~A \/ ~B).
Proof.
  split.
  + intro.
    apply NNPP.
    intro.
    apply H0.
    left.
    intro.
    apply H0.
    right.
    intro.
    apply H.
    split.
    - exact H1.
    - exact H2.
  + intro.
    intro.
    destruct H0.
    destruct H.
    - apply H. exact H0.
    - apply H. exact H1.
Qed.
```

**Exercises 29: (A -> B) -> (C -> ~B) -> (A -> ~C)**
```coq
Theorem Ex029 (A B C : Prop): (A -> B) -> (C -> ~B) -> (A -> ~C).
Proof.
  intros.
  intro.
  apply H0.
  + exact H2.
  + apply H.
    exact H1.
Qed.
```

**Exercises 30: (A -> B -> C) <-> (~C -> A -> ~B)**
```coq
Require Import Classical.

Theorem Ex030 (A B C : Prop) :  (A -> B -> C) <-> (~C -> A -> ~B).
Proof.
  split.
  + intro.
    intros.
    intro.
    apply H0.
    apply H.
    - exact H1.
    - exact H2.
  + intros.
    apply NNPP.
    intro.
    apply H.
    * exact H2.
    * exact H0.
    * exact H1.
Qed.
```

**Exercise 31: (A -> B) \\/ A <-> (B -> A) \\/ B**
```coq
Require Import Classical.

Theorem Ex031 (A B C : Prop):  (A -> B) \/ A <-> (B -> A) \/ B.
Proof.
  split.
  + intro.
    destruct H.
    - apply NNPP.
      intro.
      apply H0.
      left.
      intro.
      apply NNPP.
      intro.
      apply H0.
      right.
      exact H1.
    - left.
      intro.
      exact H.
  + intro.
    destruct H.
    - apply NNPP.
      intro.
      apply H0.
      left.
      intro.
      apply NNPP.
      intro.
      apply H0.
      right.
      exact H1.
    - left.
      intro.
      exact H.
Qed.
```

**Exercise 32: ((A /\ B ) -> C) <-> ((A -> C) \\/ (~C -> ~B))**
```coq
Require Import Classical.

Theorem Ex032 (A B C : Prop): ((A /\ B ) -> C) <-> ((A -> C) \/ (~C -> ~B)).
Proof.
  split.
  + intro.
    apply NNPP.
    intro.
    apply H0.
    left.
    intro.
    apply H.
    split.
    - exact H1.
    - apply NNPP.
      intro. 
      apply H0.
      right.
      intro.
      exact H2.
  + intros.
    destruct H0.
    destruct H.
    - apply H.
      exact H0.
    - apply NNPP.
      intro.
      apply H.
      * exact H2.
      * exact H1.
Qed.
```

**Exercise 33: ((A /\ (B -> C )) -> A) <-> ((A /\ (B -> ~C)) -> A)**
```coq
Theorem Ex033 (A B C : Prop): ((A /\ (B -> C )) -> A) <-> ((A /\ (B -> ~C)) -> A).
Proof.
  split.
  + intros.
    destruct H0.
    exact H0.
  + intros.
    destruct H0.
    exact H0.
Qed.
```

**Exercise 34: (A \/ ((B -> C) /\ D)) -> ((B \/ A) \/ (~C -> D))**
```coq
Theorem Ex034 (A B C D : Prop) : (A \/ ((B -> C) /\ D)) -> ((B \/ A) \/ (~C -> D)).
Proof.
  intros.
  destruct H.
  + left. right. exact H.
  + destruct H.
    right. intro. exact H0.
Qed.
```

**Exercise 35: A -> True**
```coq
Theorem Ex035 (A : Prop) : A -> True.
Proof.
  intro.
  apply I.
Qed.
```

**Exercise 36: (A -> B) -> A -> B**
```coq
Theorem Ex036 (A B : Prop): (A -> B) -> A -> B.
Proof.
  intros.
  apply H.
  exact H0.
Qed.
```

**Exercise 37: A \\/ B -> ~A \\/ ~C -> C -> B**
```coq
Theorem Ex037 (A B C : Prop) :  A \/ B -> ~A \/ ~C -> C -> B.
Proof.
  intros.
  destruct H.
  + destruct H0. 
    - contradiction.
    - contradiction.
  + exact H.
Qed.
```

**Exercise 38: ~C -> ~A \\/ ((B /\ C) -> A)**
```coq
Require Import Classical.

Theorem Ex038 (A B C : Prop) :  ~C -> ~A \/ ((B /\ C) -> A).
Proof.
  intro.
  apply NNPP.
  intro.
  apply H0.
  left.
  intro.
  apply H0.
  right.
  intro.
  exact H1.
Qed.
```

**Exercise 39: ~(((A -> B) /\ A) /\ (B -> ~C /\ ~C -> B)) -> ((~D -> B) \/ (B -> (~B -> ~A)))**
```coq
Theorem Ex039 (A B C D : Prop) : ~(((A -> B) /\ A) /\ (B -> ~C /\ ~C -> B)) -> ((~D -> B) \/ (B -> (~B -> ~A))).
Proof.
  intros.
  right.
  intros.
  contradiction.
Qed.
```
**Exercise 40: (A -> B) \\/ (B -> A)**
```coq
Require Import Classical.

Theorem Ex040 (A B : Prop): (A -> B) \/ (B -> A).
Proof.
  apply NNPP.
  intro.
  apply H.
  left.
  intro.
  exfalso.
  apply H.
  right.
  intro.
  exact H0.
Qed.
```

**Exercise 41: B /\ B -> A -> ((C \\/ ~B) \\/ A <-> A /\ ~(B -> ~A))**
```coq
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
```

**Exercise 42: (~A -> False) -> A**
```coq
Require Import Classical.

Theorem Ex042 (A : Prop) : (~A -> False) -> A.
Proof.
  intro.
  apply NNPP.
  intro.
  apply H.
  exact H0.
Qed.
```

**Exercise 43: A /\ B -> ~A \\/ C -> ~(A /\ B) -> ~C**
```coq
Theorem Ex043 (A B C : Prop): A /\ B -> ~A \/ C -> ~(A /\ B) -> ~C.
Proof.
  intros.
  intro.
  destruct H.
  apply H1.
  split.
  + exact H.
  + exact H3.
Qed.
```
**Exercise 44: \~(\~(A -> B) /\ ~B) -> (~C -> A) -> C \\/ B**
```coq
Require Import Classical.

Theorem Ex044 (A B C : Prop) :  ~(~(A -> B) /\ ~B) -> (~C -> A) -> C \/ B.
Proof.
  intros.
  apply NNPP.
  intro.
  apply H.
  split.
  + intro.
    apply H1.
    right.
    apply H2.
    apply H0.
    intro.
    apply H1.
    left. exact H3.
  + intro.
    apply H1.
    right. exact H2.
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
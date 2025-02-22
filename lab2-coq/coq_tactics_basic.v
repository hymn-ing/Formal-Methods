Theorem example1: forall P:Prop,
    P -> P.
Proof.
    intros.
    apply H.
Qed.

Theorem example1a: forall P Q:Prop,
    P -> (Q -> P).
Proof.
    intros.
    apply H.
Qed.


Theorem example2: forall P Q: Prop,
    (P -> Q) -> P -> Q.
Proof.
    intros.
    apply H in H0.
    apply H0.
Qed.

Theorem example2a: forall P Q H:Prop,
    (P->Q) -> (Q->H) -> (P->H).
Proof.
    intros.
    apply H0 in H2.
    apply H1 in H2.
    apply H2.
Qed.

Theorem example3: forall P Q: Prop,
    P/\Q -> Q.
Proof.
    intros.
    inversion H.
    apply H1.
Qed.

Theorem example3a: forall P Q: Prop,
    P /\ (P -> Q) -> Q.
Proof.
    intros.
    inversion H.
    apply H1 in H0.
    apply H0.
Qed.

Theorem example4: forall P Q:Prop,
    (P /\ Q) -> (Q /\ P).
Proof.
    intros.
    inversion H.
    split.
    apply H1.
    apply H0.
Qed.

Theorem Exercise4: forall P Q R:Prop,
    (P /\ (Q /\ R)) -> ((P /\ Q) /\ R).
Proof.
    intros.
    inversion H.
    inversion H1.
    split.
    split.
    apply H0.
    apply H2.
    apply H3.
Qed.

Theorem example5: forall P Q: Prop,
    (P \/ Q) -> (Q \/ P).
Proof.
    intros.
    inversion H.
    right.
    apply H0.
    left.
    apply H0.
Qed.

Theorem exercise5: forall P Q R: Prop,
    (P \/ (Q \/ R)) -> ((P \/ Q) \/ R).
Proof.
    intros.
    inversion H.
    left.
    left.
    apply H0.
    inversion H0.
    left.
    right.
    apply H1.
    right.
    apply H1.
Qed.

Theorem exercise6: forall P Q R: Prop,
    ((P -> R) /\ (Q -> R)) -> (P /\ Q -> R).
Proof.
    intros.
    inversion H.
    inversion H0.
    apply H1 in H3.
    apply H3.
Qed.

Theorem exercise7: forall P Q R: Prop,
        (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
Proof.
    intros.
    split.
    apply H.
    apply H.
Qed.

Theorem challenge1: forall P Q R:Prop,
        (P /\ Q -> R) <-> (P -> Q -> R).
Proof.
  intros.
  split.
  intros.
  apply H.
  split.
  apply H0.
  apply H1.
  intros.
  apply H.
  apply H0.
  apply H0.
Qed.

Theorem challenge2: forall P Q R:Prop,
        (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  unfold not.
  unfold not in H0.
  intros.
  apply H in H1.
  apply H0 in H1.
  apply H1.
Qed.
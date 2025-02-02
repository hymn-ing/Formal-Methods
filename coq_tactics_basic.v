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
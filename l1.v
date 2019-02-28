Section Z1.

Variables A B C : Prop.

Lemma z1l1: A -> (B -> A).
Proof.
  intros.
  assumption.
Qed.

Lemma z1l2: (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros.
  apply H.
  - assumption.
  - apply H0.
    assumption.
Qed.

Lemma z1l4: A -> ~~A.
Proof.
  intros.
  intro.
  absurd A.
  - assumption.
  - assumption.
Qed.

(* Lemma z1l7: (~A -> B) -> A *)
(*            1  1 x  0 0 *)

Lemma z1l9: ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  intros.
  apply H.
  intros.
  apply H0.
  intros.
  apply H.
  intros.
  assumption.
Qed.

Lemma z1l10: (A -> B) -> (A -> ~B) -> A -> C.
Proof.
  intros.
  absurd B.
  - apply H0; assumption.
  - apply H; assumption.
Qed.

Require Import Classical.

Lemma z1l3: (~A -> A) -> A.
Proof.
  intros.
  tauto.
Qed.

Lemma z1l5: ~~A -> A.
Proof.
  apply NNPP.
Qed.

Lemma z1l6: ~~~A -> ~A.
Proof.
  intro.
  (* tauto. *)
  intro.
  absurd A.
  - apply NNPP.
    assumption.
  - assumption.
Qed.


Lemma z1l8: ~(A -> B) -> A.
Proof.
  intros.
  apply NNPP.
  intro.
  apply H.
  intro.
  absurd A.
  - assumption.
  - assumption.
  (* tauto. *)
Qed.

End Z1.


Section Z2.

Parameter S T : Set.
Parameter A : S -> T -> Prop.
Parameter B : T -> Prop.
Parameter C : Prop.

(* Lemma z2l1: (exists x, forall y, A x y) -> forall x, exists y, A x y. *)

(* Lemma z2l2: (~forall x, B x) -> exists x, ~(B x). *)

Lemma z2l3: (exists x, ~(B x)) -> (~forall x, B x).
Proof.
  intros.
  intro.
  destruct H.
  absurd (B x).
  - assumption.
  - apply H0.
Qed.  

(* Lemma z2l4: (~exists x, B x) -> forall x, ~B x. *)

Lemma z2l5: (forall x, ~B x) -> ~exists x, B x.
Proof.
  intros.
  intro.
  destruct H0.
  absurd (B x).
  - apply H.
  - assumption.
Qed.

(* Lemma z2l6: (C -> exists x, B x) -> (exists x, C -> B x). *)
  
Lemma z2l7: (exists x, C -> B x) -> C -> exists x, B x.
Proof.
  intros.
  destruct H.
  exists x.
  apply H.
  assumption.
Qed.

(* Lemma z2l8: exists x, forall y, B x -> B y. *)


End Z2.


Section Z4.

Variables A B : Prop.

Lemma not_or: ~(A \/ B) -> ~A /\ ~B.
Proof.
  intro.
  split.
  - intro.
    apply H.
    left.
    assumption.
  - intro.
    apply H.
    right.
    assumption.
Qed.

Lemma and_not: ~A /\ ~B -> ~(A \/ B).
Proof.
  intro.
  intro.
  destruct H0 as [HA | HB].
  - absurd A.
    + apply H.
    + apply HA.
  - absurd B.
    + apply H.
    + apply HB.
Qed.

Lemma or_not: ~A \/ ~B -> ~(A /\ B).
Proof.
  intro.
  intro.
  destruct H.
  - absurd A.
    + assumption.
    + apply H0.
  - absurd B.
    + assumption.
    + apply H0.
Qed.

Require Import Classical.

Lemma not_and: ~(A /\ B) -> ~A \/ ~B.
Proof.
  intro.
  apply NNPP.
  intro.
  apply H.
  split.
  - apply NNPP.
    intro.
    apply H0.
    left.
    assumption.
  - apply NNPP.
    intro.
    apply H0.
    right.
    assumption.
Qed.


End Z4.

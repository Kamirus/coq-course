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

Lemma z1l6: ~~~A -> ~A.
Proof.
  intro.
  (* tauto. *)
  intro.
  absurd A.
  - intro.
    apply H.
    intro.
    absurd A; assumption.
  - assumption.
Qed.

(* Lemma z1l7: (~A -> B) -> A *)
(*              1  1 x  0 0 *)

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
  destruct classic with A.
  - assumption.
  - apply H.
    assumption.
Qed.

Lemma z1l5: ~~A -> A.
Proof.
  apply NNPP.
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

Require Import Classical.

Variable S T : Set.
Variable A : S -> T -> Prop.
Variable B : T -> Prop.
Variable C : Prop.

(* Lemma z2l1: (exists x, forall y, A x y) -> forall x, exists y, A x y. *)

Lemma z2l2: (~forall x, B x) -> exists x, ~(B x).
Proof.
  intro.
  apply NNPP.
  intro.
  apply H.
  intro.
  destruct classic with (B x).
  - assumption.
  - exfalso.
    apply H0.
    exists x.
    assumption.
Qed.

Lemma z2l3: (exists x, ~(B x)) -> (~forall x, B x).
Proof.
  intros.
  intro.
  destruct H.
  absurd (B x).
  - assumption.
  - apply H0.
Qed.  

Lemma z2l4: (~exists x, B x) -> forall x, ~B x.
Proof.
  intros.
  intro.
  apply H.
  exists x.
  assumption.
Qed.

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


Section Z3.

Variable T : Set.
Variable C : T -> Prop.
Variable S : T -> Prop.
Variable G : T -> T -> Prop.

Axiom a3 :
forall x, C x /\ S x ->
forall y, S y -> (~ G y y -> G x y) /\ (G y y -> ~ G x y).

Lemma z3 : 
~ exists x, C x /\ S x.
Proof.
  intro.
  destruct H.
  apply a3 with (y:=x) in H as H1.
  - apply H1; apply H1; intro; apply H1; assumption.
  - apply H.
Qed.

End Z3.


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


Section Z5.

(* Auto -
This tactic implements a Prolog-like resolution procedure to solve the current goal.
It first tries to solve the goal using the assumption tactic,
then it reduces the goal to an atomic one using intros
and introduces the newly generated hypotheses as hints.
Then it looks at the list of tactics associated to the head symbol of the goal
and tries to apply one of them (starting from the tactics with lower cost).
This process is recursively applied to the generated subgoals.

By default, auto only uses the hypotheses of the current goal and
the hints of the database named core. *)

Variables A B : Prop.

Lemma aux: A -> A /\ A /\ A /\ A /\ A.
Proof.
  (* auto 4. *)
  auto 5.
Qed.

End Z5.




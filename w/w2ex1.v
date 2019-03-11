Require Import Utf8.

Parameter P : Set.

Definition square := fun x => x*x.

Section Commands.

Hypothesis P : Prop.
Let s2 := square 2.

Definition conjunction := P /\ P.
End Commands.

(*Check s2.*)
Print conjunction.

Axiom proof_of_false : False.

Lemma lemma_false : False.
Proof.
exact proof_of_false.
Qed.


Section Logic.

Variables A B : Prop.

Goal A /\ B -> B /\ A.
Proof.
intro.
constructor.
destruct H.
assumption.
destruct H.
assumption.
Qed.

Print Unnamed_thm.

Lemma conj_symm :
A /\ B -> B /\ A.
Proof.
intro.
destruct H.
constructor; trivial.
Qed.

Print conj_symm.

Goal A /\ B -> B /\ A.
Proof.
tauto.
Qed.

Print Unnamed_thm0.


Variables P Q : Prop.

Lemma PeirceI : ((P -> Q) -> P) -> ~~ P.
Proof.
intro.
intro.
apply H0.
apply H.
intro.
exfalso.
apply H0.
assumption.
Qed.


Require Import Classical.

Lemma Peirce : ((P -> Q) -> P) -> P. 
Proof.
tauto.
Qed.

Print Peirce.

Print NNPP. 
End Logic.

Section Equational.


Variable E : Type.
Variables a b c:E.
Variable f : E*E -> E.
Variable g : E -> E.

Lemma A: f(a,b) = a -> f(f(a,b),b) = c -> g a = g c.
Proof.
intros.
rewrite H in H0.
rewrite <- H.
rewrite <- H0.
reflexivity.
(* congruence. *)
Qed.

End Equational.

Section Sets.

Variable U : Type.

Variable A B C : U -> Prop.

Definition incl A B := forall x : U, A x -> B x.

Notation " A \u2286 B " := (incl A B) (at level 80).

Lemma incl_trans : A \u2286 B -> B  \u2286 C -> A \u2286 C.
Proof.
intros.
unfold incl in *.
intros.
apply X0.
apply X.
assumption.
Qed.

End Sets.



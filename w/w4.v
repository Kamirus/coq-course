Require Import Arith.

(* operatory logiczne *)
(* True *)
Print True.
Check True_ind.
Print True_rect.

Scheme Trueind := Induction for True Sort Prop.
Print Trueind.

(* False *)

Print False.

Lemma efq :
False -> 2+2=5.
Proof.
contradiction.
(* induction 1.*)
(* destruct 1. *)
(* intro f; case f. *)
Qed.

Lemma efq_nat:
False -> nat.
intro.
destruct H.
Defined.

Print False_ind.
Print efq.

Axiom bottom:False.

Eval compute in efq bottom.
Eval compute in efq_nat bottom.


Scheme Falseind := Induction for False Sort Prop.
Print Falseind.

(* negacja *)

Print not.
Locate "~".

(* koniunkcja *)

Print and.
Check conj.
Locate "/\".

Check and_ind.
Check prod_ind.
Print and_rect.
Print prod_rect.

Lemma and_fst :
forall A B : Prop, A /\ B -> A.
Proof.
intros.
(*destruct H. *)
induction H.
assumption.
Qed.

Print and_fst.

(* alternatywa *)

Print or.
Check or_introl.
Check or_intror.
Locate "\/".

Lemma or_right:
forall A B : Prop, A -> B \/ A.
Proof.
intros.
constructor 2.
assumption.
Qed.

Print or_right.

Lemma or_id :
forall A : Prop, A \/ A -> A.
Proof.
intros.
destruct H.
assumption.
assumption.
(* induction H; assumption. *)
Qed.

Print or_id.
Print or_ind.

(* exists *)

Locate "exists".
Print ex.

Lemma ex_gt :
forall n:nat, exists m:nat, m > n.
Proof.
intros.
exists (S n).
auto.
Qed.

Print ex_gt.
Print le_n.
Print lt.

Lemma ex_elim :
forall m:nat, (exists n:nat, n + 3 = m) -> m > 2. 
Proof.
intros.
(*elim H; intros.*)
destruct H.
rewrite <- H.
auto with arith.
Qed.


Print ex_elim.
Print le_plus_r.


Print unique.

Lemma ex_unique :
forall n:nat, n > 0 -> exists ! m:nat, S m = n.
intro n; case n; intros.
inversion H.
unfold unique.
(* exists n0. *)
split with n0.
split; intros; congruence.
Qed.


(* rownosc *)



Print eq.

Locate "=".

Check eq_ind.
Print eq_rect.

Lemma eq_refl :
forall A (x:A), x = x.
Proof.
reflexivity.
Qed.

Lemma eq_sym :
forall A (x y:A), x = y -> y = x.
Proof.
intros.
induction H. 
reflexivity.
Qed.

Print eq_sym.

Lemma eq_trans :
forall A (x y z:A), x = y -> y = z -> x = z.
Proof.
intros.
(*replace x with y.
assumption.*)
induction H.
assumption.
Qed.

Print eq_trans.

Lemma eq_conv :
2+4 = 6.
apply eq_refl.
Qed.

Print eq_conv.
Check eq_refl.


(* even *)

Inductive even : nat -> Prop :=
| even0 : even 0
| evenSS : forall n:nat, even n -> even (S (S n)).

Check even_ind.

Hint Constructors even.

Print HintDb core.

Lemma even_6 :
even 6.
Proof.
auto.
(*repeat constructor.*)
Qed.

Lemma even_1_impossible1 :
even 1 -> False.
Proof.
intro He1.
Show Proof.
induction He1.
Show Proof.
Abort.

Check even_ind.

Lemma even_1_impossible3 :
forall n:nat, even n -> n=1 -> False.
Proof.
intros n Hen.
induction Hen.
discriminate.
discriminate.
Qed.

Lemma even_1_impossible2 :
even 1 -> False.
Proof.
intro He1.
inversion He1.
Show Proof.
Qed.

Print even_1_impossible2.


Lemma even_1_impossible4 :
even 1 -> False.
Proof.
intro.
generalize (refl_equal 1).
pattern 1 at 1.
induction H.
Show Proof.
discriminate.
discriminate.
Qed.


Lemma even_SS_n :
forall n, even (S (S n)) -> even n.
Proof.
intros.
inversion H.
subst.
assumption.
Qed.

Lemma even_sum :
forall n m, even n -> even m -> even (n+m).
Proof.
(*induction n; intros; auto.*)
induction 1. intros.
assumption.
simpl.
intro. apply evenSS.
(* constructor. *)
apply IHeven.
assumption.
Qed.

Fixpoint F (n m:nat) (p:even n) (q:even m) : even (n+m) :=
match p (* in (even n) return (even (n+m)) *) with
| even0 => q
| evenSS n0 p0 => evenSS _ (F n0 m p0 q)
end. 

Lemma even_impossible :
forall n, even (S (n+n)) -> False.
Proof.
induction n.
- inversion 1.
- intro.
  apply IHn.
  simpl in H.
  inversion H. subst.
  (* inversion_clear H. *)
  replace (S (n+n)) with (n+S n).
  * assumption.
  * auto.
Qed.

Lemma even_impossible12 :
forall n, even n -> forall m, n = S (m+m) -> False.
Proof.
  induction 1.
  - intros; inversion H.
  - intros.
    injection H0.
    intro.
    destruct m.
    * discriminate H1.
    * simpl in H1; injection H1; intro.
      apply IHeven with m.
      rewrite H2.
      auto.
Qed.

Lemma even_impossible2 :
forall n m, even n -> n = S (m+m) -> False.
Proof.
(*induction 1.
discriminate.
intros.
injection H0.
intros.*)
(* zmienna m jest ustalona *)
intros.
generalize m H0.
clear m H0.
induction H.
intros; discriminate.
intros.
injection H0.
intros.
destruct m.
discriminate.
simpl in H1; injection H1; intros.
apply IHeven with m.
rewrite H2.
auto.
Qed.

(* niedozwolna eliminacja z Prop w Set 

Definition or_bool (A B:Prop) (p: A \/ B) : bool :=
match p with
| or_introl x => true
| or_intror y => false
end.
*)


(* tak tez nie mozna

Lemma or_bool :
forall A B:Prop, A \/ B -> bool.
Proof.
intros.
destruct H.
*)

(* <= *)

Print le.

Lemma le_trans :
forall n m, n <= m -> forall p, m <= p -> n <= p.
Proof.
induction 2.
auto.
constructor.
auto.
Qed.


(* dokumentacja
https://coq.inria.fr/distrib/current/refman/index.html 
*)

Check Set.
Check Prop.
Check Type.


Section Logic.

Variables A B C : Prop.

Check True.
Check False.
Check and.
Check or.
Check not.

Check (A \/ B).
Check (A /\ B).
Check (A -> B).

Search "/\".

Lemma id_auto:
A -> A.
Proof.
auto.
Qed.

Lemma id_2:
A -> A.
Proof.
intro.
assumption.
Qed.

Print id_2.

Lemma contraction:
A /\ A -> A.
Proof.
intro.
destruct H.
assumption.
Qed.

Lemma apply:
(A -> B) -> A -> B.
Proof.
intros H1 H2.
apply H1.
assumption.
Qed.

Print apply.


Variable T : Type.
Variable P Q : T -> Prop.

Lemma first_order:
(forall x, P x) \/ (forall x, Q x) -> forall x, P x \/ Q x.
Proof.
intros.
destruct H.
left.
apply H.
right.
apply H.
Qed.

End Logic.

Section Nats.

Check nat.
Check 0.
Check (fun x => x).
Check (fun x => x + 0).

Definition double := fun x => x * 2.
Check double.

Eval compute in (double 4).

(* Popraw definicje compose *)

(* Definition compose := fun f => fun g => fun x => f (g x).*)

End Nats.

Section Lambda.

Variable L : Type.
Variable red_trans_refl : L -> L -> Prop. (* ->*_beta *)

(* Uzupelnij definicje *)

(* t jest w postaci normalnej *)
Definition normal t : Prop := 
.

(* red_trans_refl jest konfluentna *)
Definition confluent : Prop := 
.

(* t ma postac normalna *)
Definition has_normal  t : Prop := 
.

(* Zapisz lemat: istnieje term, ktory nie ma postaci normalnej *)

End Lambda.







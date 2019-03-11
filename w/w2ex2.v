Require Import Utf8.

(* sorty *)
Check Set.
Check Prop.
Check Type.

(* typy danych : Set *)
Check nat.
Check bool.
Check nat -> bool.

(* formuly logiczne : Prop *)
Check True.
Check False.
Check True \/ False.
Check forall n:nat, n > 0.
(*Check forall n, n = n.
Check forall:nat, O. *)
Check forall n, n = nat.

(* rozne termy *)
Check fun n:nat => n.
Check fun b:bool => Set.
Check plus.
Check plus 0 7.
Check fun _ n : nat => n.
Check let x:=4 in x*x.

Definition pred (n:nat) :=
match n with
| O => O
| S n => n
end.

Check pred.
Eval compute in pred 4.

Definition nattype (n:nat) :=
match n with
| O => nat
| S O => bool
| _ => nat -> bool
end.

Check nattype.
Eval compute in (nattype O).
Eval compute in (nattype 1).
Eval compute in (nattype (3+5)).


Section arith.

Definition natprop (n:nat) : Prop := 
match n with
| O => True
| S n => O = O
end.

Lemma natprop_S:
forall n:nat, natprop (S n).
Proof.
simpl.
intro n.
reflexivity.
Qed.

Section more_logic.

Variables A B C : Prop.

Lemma conj_assoc :
(A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
split; intros.
* destruct H as [[H1a H1b] H2].
  repeat split; assumption.
* destruct H as [H1 [H2a H2b]].
  repeat split; assumption.
Qed.

Print conj_assoc.


Lemma exists_even :
exists n, exists k, n = k + k.
Proof.
exists 4.
exists 2.
simpl.
reflexivity.
Qed.

Print exists_even.

End more_logic.


Definition id := fun n:nat => n.

Lemma prove_nat :
nat.
Proof.
exact (id 3).
Qed.
(*Defined.*)

Print prove_nat.
Eval compute in prove_nat.

Definition proof_of_impl (A:Prop) : A -> A :=
fun x => x.

Print proof_of_impl.




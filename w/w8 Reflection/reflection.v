Require Import Arith.
Require Import List.
Require Import FunInd.

(* obliczenie nie zostawia "sladu" w dowodzie *)

Fact triv :
forall n, 0 + n = n.
Proof.
intro n.
rewrite plus_O_n.
reflexivity.
Qed.

Print triv.

Fact triv' :
forall n, 0 + n = n.
Proof.
intro n.
reflexivity.
Qed.

Print triv'.

Inductive even : nat -> Prop :=
| evenO : even O
| evenSS : forall n, even n -> even (S (S n)).

Hint Constructors even.

Lemma even1046: even 1046.
Time repeat constructor.
Qed.

Print even1046.

(* dowod przez refleksje - slaba specyfikacja *)

Function check_even (n:nat) : bool :=
match n with
| O => true
| 1 => false
| S (S n0) => check_even n0
end.

Lemma check_even_correct :
forall n, check_even n = true -> even n.
Proof.
intro n.
functional induction (check_even n); intros; auto. discriminate.
Qed.  

Ltac prove_even n :=
  exact (check_even_correct n (refl_equal true)).

Lemma even4000 :
even 4000.
Proof.
(*Time repeat constructor.*)
Time prove_even 4000.
(* wystarczy sprawdzic, czy check_even 4000 = true *)
Qed.

Print even4000.

Lemma false_even1247 :
even 1247.
Proof.
(*prove_even 1247.*)
Abort.

(* silna specyfikacja *) 

Inductive option (P:Prop) : Set :=
| proof : P -> option P
| noproof : option P.

Definition get_form {P} (x: option P) : Prop :=
match x with
| proof _ p => P
| noproof _ => True
end.


Definition get_proof {P} (x: option P) : get_form x :=
match x with
| proof _ p => p
| noproof _ => I
end.

Eval compute in get_form (proof _ (refl_equal 0)).
Eval compute in get_proof (proof _ (refl_equal 0)).
Eval compute in get_form (noproof (0=0)).

Notation " x <- a1 ; a2 " := 
(match a1 with
| proof _ x => a2
| noproof _ => _
end) (at level 60).

Notation " [ x ] " := (proof _ x).
Notation " ! " := (@noproof _).

Definition check_even' : forall (n:nat), option (even n).
refine (fix check n : option (even n) :=
match n with
| 0 => [evenO]
| 1 => ! 
| S (S n0) => 
p <- check n0; [evenSS _ p] 
end).
destruct (check n0); [repeat constructor | constructor 2]; trivial.
Defined. 

Eval compute in (check_even' 32).
Eval compute in (check_even' 33).

Eval compute in (get_proof (check_even' 32)).
Eval compute in (get_form (check_even' 32)).
Eval compute in (get_proof (check_even' 33)).

Ltac prove_even_strong :=
match goal with
| [ |- even ?n ] => exact (get_proof (check_even' n))
end. 

Lemma strong_even4000 :
even 4000.
Proof.
Time prove_even_strong.
Time Defined.

Print strong_even4000.
(*Eval compute in strong_even4000.*)

Lemma even17 :
even 17.
Proof.
(*prove_even_strong.*)
Abort.

Require Import Bool.
Print reflect.

Check reflect (even 2) (check_even 2).

Lemma even_reflect :
forall n, reflect (even n) (check_even n).
Proof.
intro n.
Check iff_reflect.
apply iff_reflect.
split.
- induction 1; auto.
- apply check_even_correct.
Qed.

Lemma even1046_reflect :
even 1046.
Proof.
assert (hh:=even_reflect 1046).
inversion hh.
trivial.
Time Qed.

Print even1046_reflect.






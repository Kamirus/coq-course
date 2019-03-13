(* indukcyjne typy danych *)

Print nat.


Check nat_ind.
Print nat_ind.

Check nat_rect.
Check nat_rec.
Print nat_rec.
Print nat_rect.

Check S.
Check (S 5).

(* iota *)
Definition zero (n:nat) : Prop :=
match n with
| O => True
| S _ => False
end.

Eval cbv delta in (zero 2).
Eval cbv delta beta in (zero 2).
Eval cbv delta beta iota in (zero 2).

Definition zero2 : nat -> Prop := 
nat_rect (fun n:nat=>Prop) True (fun n H => False).

Eval compute in (zero2 2).


Fixpoint fact (n:nat) : nat :=
match n with
| 0 => 1
| S m => n * fact m
end.

Locate "*".

Eval cbv delta [fact] in (fact 3).
Eval cbv delta [fact] beta iota in (fact 3).
Eval cbv delta [fact] iota beta delta [mult] in (fact 3).


(* induction *)

Require Import Nat.
Print add.

Lemma plus_n_0_1 :
forall n:nat, plus n 0 = n.
Proof.
induction n.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Print plus_n_0_1.

Lemma plus_n_0_2 :
forall n:nat, plus n 0 = n.
Proof.
info_auto.
Qed.

Print plus_n_0_2.


Lemma id :
forall n:nat, nat.
Proof.
intro n.
induction n.
constructor.
constructor 2.
assumption.
Defined.

Print id.

Eval compute in id 3.

(* elim *)

Lemma mult_n_1 :
forall n:nat, mult n 1 = n.
Proof.
intro n.
elim n.
trivial.
intros m IHm.
simpl.
rewrite IHm.
trivial.
Qed.

Print mult_n_1.

(* case *)

Lemma nat_0_or_S :
forall n:nat, n=0 \/ exists m:nat, n = S m.
Proof.
intro n.
case n.
left; trivial.
right.
split with n0.
trivial.
Qed.

Print nat_0_or_S.


Lemma nat_0_or_S2 :
forall n:nat, n=0 \/ exists m:nat, n = S m.
Proof.
intro n.
destruct n.
left; trivial.
right.
split with n; trivial.
Qed.

Print nat_0_or_S2.

(* discriminate *)

Lemma one_not_zero :
0 = (fun x:nat => S x) 0 -> False.
Proof.
intro.
discriminate.
Qed.

Definition notzero (n:nat) : Prop :=
match n with
| 0 => False
| _ => True
end.

Lemma one_not_zero2 :
0 = 1 -> False.
Proof.
intro Heq01.
change (notzero 0).
rewrite Heq01.
simpl.
trivial.
Qed.


(* injection *)

Lemma inj_nat :
forall n m:nat, S n = S m -> n = m.
Proof.
intros n m Heq.
injection Heq.
trivial.
Qed.

Definition aux (n:nat) : nat := 
match n with
| O => O
| S m => m
end.

Lemma inj_nat2 :
forall n m:nat, S n = S m -> n = m.
Proof.
intros n m Heq.
change n with (aux (S n)).
change m with (aux (S m)).
rewrite Heq.
reflexivity.
Qed.

(* constructor *)

Lemma nat_exists : 
nat.
Proof.
constructor.
Qed.

Print nat_exists.

Lemma nat_exists_S :
nat.
Proof.
constructor 2.
apply O.
Qed.

Print nat_exists_S.




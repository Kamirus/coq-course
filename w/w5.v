Require Import List.
Require Import Arith.
Require Import ProofIrrelevance.
Require Extraction.

Import ListNotations.

(* Typ list indeksowanych dlugoscia *)

(*
Inductive llist (A:Set) : nat -> Set :=
| lnil : llist A 0
| lcons : forall n, A -> llist A n -> llist A (S n).
*)


Inductive llist {A:Set} : nat -> Set :=
| lnil : llist 0
| lcons : forall n, A -> llist n -> llist (S n).

Check llist.
Check @llist.
Arguments lcons [_ n].

Check [].

Notation "[]" := lnil : myscope.
Infix "::" := lcons (at level 60, right associativity) : myscope.

Open Scope myscope.

Check [].

Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : myscope.

Definition length A n (l: @llist A n) := n.

Check length.

Fixpoint append {A n1 n2} (l1: @llist A n1) (l2: @llist A n2) : @llist A (n1+n2) :=
match l1 (*in llist n1 return llist (n1+n2)*)  with
| [] => l2
| x :: l' => x :: (append l' l2) 
end.

(*
Fixpoint reverse {A} n (l:@llist A n) : @llist A n :=
match l with
| [] => []
| x :: l' => append (reverse _ l') [x]
end.
*)


Fixpoint reverse {A} n (l:@llist A n) : @llist A n.
refine (match l in llist n return llist n with
| [] => []
| x :: l' => _ 
end).
rewrite <- Nat.add_1_r.
apply append.
exact (reverse _ _ l').
exact [x].
Defined.


Print reverse.


Require Import Equality.
Import EqNotations.


Fixpoint reverse2 {A} n (l:@llist A n) : @llist A n :=
match l in llist n return llist n with
| [] => []
| @lcons _ m x  l' => 
rew  (Nat.add_1_r m) in (append (reverse2 _ l') [x])
end.

Compute reverse2 1 [3].
Compute reverse2 2 [2;3].

Extraction reverse2.


Lemma add_1 :
forall n, n + 1 = S n.
induction n; simpl; auto.
Defined.

Compute add_1 1.

Fixpoint reverse3 {A} n (l:@llist A n) : @llist A n :=
match l in llist n return llist n with
| [] => []
| @lcons _ m x  l' => rew  (add_1 m) in (append (reverse3 _ l') [x])
end.

Compute reverse3 _ [1;2;3].


Definition hd {A} {n} (l: @llist A (S n)) : A := 
match l with
| x :: _ => x
end.

Print hd.
Print IDProp.

(*Check hd [].*)

Check hd _.


Definition hd' {A} n (l: @llist A n) : 
  match n with
  | 0 => unit
  | _ => A
  end
:=
match l with
| [] => tt
| x :: _ => x
end.

Check hd'.
Check hd' _ [].

Definition hd2 {A} n (l : @llist A (S n)) : A := hd' (S n) l.

Definition tl {A} n (l : @llist A (S n)) :=
match l with
| _ :: l' => l'
end.

Definition tl' {A} n (l: llist n) : 
  match n with
  | 0 => unit
  | S m => @llist A m
  end
:=
match l (*in llist n return match n with 0 => unit | S m => @llist A m end*)  with
| [] => tt
| _ :: l' => l'
end.

Definition tl2 {A} n (l : @llist A (S n)) : @llist A n := tl' (S n) l.

Eval compute in hd [3;4].
Eval compute in tl _ [3;4].


Lemma llist_injection :
forall A n (l1 l2:@llist A n) x y, x :: l1  = y :: l2 -> x = y /\ l1 = l2. 
Proof.
intros.
injection H; intros.
(*inversion_sigma.
replace H2 with (@eq_refl nat n) in H3.
simpl in H3.
split; assumption.
apply proof_irrelevance.
*)
split; try assumption.
change (tl _ (x::l1) = tl _ (y::l2)).
rewrite H.
trivial.
Qed.

(* sumbool *)

Print sumbool.

Extraction sumbool.

(* rozstrzygalna rownosc *)

Lemma eq_nat_dec2 :
forall n m:nat, {n = m} + {n <> m}.
Proof.
(*decide equality.*)
induction n.
intro m; destruct m.
left; reflexivity.
right; auto.
intro m; destruct m.
right; auto.
destruct (IHn m).
left; congruence.
right; auto.
Defined.

Extraction eq_nat_dec2.


Lemma eq_nat_dec2_prop :
forall n m:nat, (n = m) \/ (n <> m).
Proof.
(*decide equality.*)
induction n.
intro m; destruct m.
left; reflexivity.
right; auto.
intro m; destruct m.
right; auto.
destruct (IHn m).
left; congruence.
right; auto.
Defined.

Extraction eq_nat_dec2_prop.

Notation " 'true' " := (left _ _).
Notation " 'false' " := (right _ _).

Definition eq_nat_dec3 :
forall n m:nat, {n = m} + {n <> m}.
refine
(fix F (n m:nat) : {n = m} + {n <> m} :=
match n, m with
| 0, 0 => true
| S n', S m' => if F n' m' then true else false
| _, _ => false
end); auto.
Defined.

Extraction eq_nat_dec3.


Section A_dec_eq.

Variable A : Type.
Hypothesis eq_A_dec :
forall (a b:A), {a = b} + {a <> b}.


Lemma eq_list_dec :
forall (l1 l2:list A), {l1 = l2} + {l1 <> l2}.
Proof.
decide equality.
Qed.

End A_dec_eq.

Check eq_list_dec.


Check le_lt_dec.

Definition max (n m:nat) :=
if le_lt_dec n m (* n<=m *)
then m
else n.

Eval compute in max 3 5.

Lemma le_max :
forall n m, n <= m -> max n m = m.
Proof.
intros.
unfold max.
elim (le_lt_dec n m).
trivial.
intro; absurd (m<m); eauto with arith.
Qed.

(* wyrazenia arytmetyczne *)

Inductive tp : Set := 
| Nat
| Bool
| Prod : tp -> tp -> tp.

Inductive exp : tp -> Set :=
| num : nat -> exp Nat
| add : exp Nat -> exp Nat -> exp Nat
| bval : bool -> exp Bool
| and : exp Bool -> exp Bool -> exp Bool
| isz : exp Nat -> exp Bool
| pair : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2).

Notation " '#' n " := (num n) (at level 45) : exp_scope.
Notation " a1 + a2 " := (add a1 a2) (at level 50, left associativity) : exp_scope.
Notation " b1 & b2 " := (and b1 b2) (at level 40, left associativity) : exp_scope.
Notation " 0 ? a " := (isz a) (at level 37, no associativity) : exp_scope.
Notation "[ x ; .. ; y ]" := (add x .. (add y (num 0)) ..) : exp_scope.

(*Check add (num 3) (bval true).*)

Open Scope exp_scope.

Fixpoint interpret_tp (t:tp) : Set := 
match t with
| Nat => nat
| Bool => bool
| Prod t1 t2 => prod (interpret_tp t1) (interpret_tp t2)
end.

Eval compute in interpret_tp (Prod Nat Nat).

Locate "&&".

Fixpoint eval {t:tp} (e:exp t) : interpret_tp t :=
match e in exp t return interpret_tp t with
| #n => n
| a1 + a2 => (eval a1 + eval a2)%nat
| bval b => b
| b1 & b2 => (eval b1 && eval b2)%bool
| 0? a => beq_nat (eval a) 0
| pair _ _ e1 e2 => (eval e1, eval e2)
end.

Eval compute in eval [#1;#2;#3;#4].
Eval compute in eval (pair _ _ (#1) (#2)).

Definition unpair t1 t2 (p:exp (Prod t1 t2)) : exp t1 * exp t2 :=
match p with
| pair _ _ e1 e2 => (e1, e2)
end.

Print unpair.

Close Scope exp_scope.





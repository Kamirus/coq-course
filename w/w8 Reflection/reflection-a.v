Require Import Arith.

Lemma assoc_test : 
forall x y z t u : nat, x + (y + z + (t + u)) = x + y + (z + (t + u)). 
Proof.
intros; repeat rewrite plus_assoc; auto.
Qed.

Print assoc_test.

Inductive btree : Set := 
| leaf : nat -> btree
| node : btree -> btree -> btree.

Notation " # n  " := (leaf n) (at level 60). 
Notation " [ l , r ] " := (node l r). 

Fixpoint flatten_aux (t acc : btree) : btree :=
  match t with
    | #_ => [t, acc]
    | [t1, t2] => flatten_aux t1 (flatten_aux t2 acc)
  end.

Fixpoint flatten (t : btree) : btree :=
  match t with
  | #_ => t
  | [t1, t2] => flatten_aux t1 (flatten t2)
  end.

Eval compute in (flatten [[[ #2 ,[ #3 , #4 ]],[[ #5 , #6 ], #7 ]], #1 ]).

Fixpoint interpret (t : btree) : nat :=
  match t with
  | #n => n
  | [t1, t2] => interpret t1 + interpret t2
  end.

Lemma flatten_aux_correct : 
  forall t t' : btree, interpret t + interpret t' = interpret (flatten_aux t t').
Proof.
double induction t t'; intros; simpl;
repeat match goal with
| [ H : context [ _ = interpret (flatten_aux _ _)] |- _ ] => rewrite <- H
end; auto with arith.
Qed.

Hint Rewrite <- flatten_aux_correct : mydb.

Theorem flatten_correct : 
forall t t' : btree, interpret (flatten t) = interpret (flatten t') ->
  interpret t = interpret t'.
Proof.
assert (forall t, interpret t = interpret (flatten t)) by
(induction t; simpl; try autorewrite with mydb; auto).
intros; do 2 rewrite <- H in *; trivial. 
Qed.

Ltac reify v :=
  match v with
  | (?X1 + ?X2) => 
     let r1 := reify X1 with r2 := reify X2 
     in constr:([r1, r2])
  | ?X1 => constr: (#X1)
  end.

Goal forall n m k:nat, n + (m + k) = (k + n) + m.
Proof.
intros.
let t := reify (n + (m + k)) in idtac t.
let t := reify ((k + n) + m) in idtac t.
Abort.

Ltac assoc_eq_nat :=
  intros;
  match goal with
  | [ |- (?X1 = ?X2 : nat) ] => 
       let t1 := reify X1 with t2 := reify X2
      in (change (interpret t1 = interpret t2); 
          apply flatten_correct;
          reflexivity)
  | _ => idtac "blad: A-rownosc nie zachodzi"
  end.

Lemma reflection_test : forall f x y z t u, 
  (f x + x) + (1 + y + z + (t + u)) = f x + x + 1 + y + (z + (t + u)).
Proof.
(*assoc_eq_nat.*)
intros.
let t1:=reify ((f x + x) + (1 + y + z + (t + u)))
with t2:=reify (f x + x + 1 + y + (z + (t + u)))
in change (interpret t1 = interpret t2).
apply flatten_correct.
simpl (flatten _).
reflexivity.
Qed.

Print reflection_test.

Lemma reflection_test' : forall f x y z t u, 
  (f x + x) + (1 + y + z + (t + u)) = f x + x + 1 + y + (z + (t + u)).
Proof.
intros.
ring.
Qed.

Print reflection_test'.

(* tylko normalizujemy *)

Ltac assoc_eq_nat_norm :=
  intros;
  match goal with
  | [ |- (?X1 = ?X2 : nat) ] => 
       let t1 := reify X1 with t2 := reify X2
      in (change (interpret t1 = interpret t2);
          apply flatten_correct; simpl)
  end.


Lemma reflection_test_norm : forall f x y z t u, 
  (f x + x) + (1 + y + z + (t + u)) = f x + x + 1 + y + (z + (t + u)).
Proof.
assoc_eq_nat_norm.
reflexivity.
Qed.

Lemma reflection_test_fail :
forall n m, (n + m) + n = m + (n + n).
Proof.
assoc_eq_nat.
assoc_eq_nat_norm.
Abort.



Require Import Bool.
Require Import Arith.
Require Import Peano.


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

Open Scope exp_scope.

Fixpoint interpret_tp (t:tp) : Set := 
match t with
| Nat => nat
| Bool => bool
| Prod t1 t2 => prod (interpret_tp t1) (interpret_tp t2)
end.


Fixpoint eval {t:tp} (e:exp t) : interpret_tp t :=
match e in exp t return interpret_tp t with
| #n => n
| a1 + a2 => (eval a1 + eval a2)%nat
| bval b => b
| b1 & b2 => (eval b1 && eval b2)%bool
| 0? a => beq_nat (eval a) 0
| pair _ _ e1 e2 => (eval e1, eval e2)
end.

Reserved Notation " t ==> t' " (at level 80).

(* semantyka naturalna wyrazen *)
Inductive evalR : forall {t}, exp t -> interpret_tp t -> Prop :=
| re_num : forall n, 
           #n ==> n
| re_add : forall a1 a2 n1 n2, 
           a1 ==> n1 -> a2 ==> n2 ->
           a1 + a2 ==> (n1 + n2)%nat
| re_bval : forall b, 
            bval b ==> b
| re_and : forall b1 b2 t1 t2, 
           b1 ==> t1 -> b2 ==> t2 ->
           b1 & b2 ==> t1 && t2
| re_isz : forall a n, 
           a ==> n -> (0? a) ==> beq_nat n 0
| re_pair : forall t1 t2 (a1: exp t1) (a2: exp t2) n1 n2, 
            a1 ==> n1 -> a2 ==> n2 -> 
            (pair _ _ a1 a2) ==> (n1, n2)
where " t ==> t' " := (evalR t t').

(* proste makro do wykanczania dowodow indukcyjnych *)
Ltac finish :=
simpl in *; try subst; try constructor; try congruence; auto.

(* ta taktyka sama wyszukuje kandydatow do indukcji *)
Ltac induct_eval tac :=
match goal with
| [ H : eval ?X = _ |- _ ] => induction X; tac
| [ H : evalR _ _ |- _ ] => induction H; tac
| _ => fail
end.

Lemma equiv :
forall t (e:exp t) v, eval e = v <-> evalR e v.
Proof.
(* intros t e v; split; intro H.
induction e; finish.
induction H; finish.*)
split; intros; induct_eval finish.
Qed.

Require Import Coq.Program.Equality.


Lemma evalR_add : 
forall (e1 e2: exp Nat) (n1 n2:nat), evalR e1 n1 -> evalR e2 n2 -> evalR (e1 + e2) ((n1 + n2)%nat).
(* induction e1. *)
dependent induction e1; intros; constructor; trivial.
Qed.

Hint Resolve evalR_add.


Lemma evalR_nat :
forall n, evalR (#n) n.
constructor.
Qed.

Hint Immediate evalR_nat.

Print HintDb core.


Lemma guess :
exists e1 e2: exp Nat, evalR (e1 + e2) ((2 + 3)%nat).
Proof.
debug eauto.
Qed.

Print guess.

(**)

Check ((2+3)%nat).

Close Scope exp_scope.

Check (2+3).

(* przypisujemy klucz do naszego zakresu *)
Delimit Scope exp_scope with exp.

(* tak uzywamy klucza, zeby skorzystac z notacji, gdy zakres nie jest otwarty *)

Check ([#3; #4])%exp.

(* Bazy twierdzen *)

(* Hint Constructors *)

Inductive even : nat -> Prop :=
| even0 : even 0
| evenSS : forall n, even n -> even (S (S n)).

(* dzieki temu auto bedzie widzialo konstruktory even *)
Hint Constructors even.

Print HintDb core.

Lemma even6 :
even 6.
Proof. auto. Qed.

(* Hint Immediate *)

Hypothesis n_1_m_1 : forall n m, n + 1 = m + 1 -> n = m.

(* podpowiedz dla auto, o niskim koszcie *)
Hint Immediate n_1_m_1 : mydb.

Print HintDb mydb.

Lemma n_1_m_1_ex :
forall n m, S (n + 1) = S (m + 1) -> n = m.
Proof.
intros n m H; injection H; intros.
info_auto with mydb.
(* samo auto nie dziala *)
Qed.

(* Hint Resolve *)

(* podpowiedz dla auto *)
Hint Resolve n_1_m_1_ex : mydb.

Print HintDb mydb.

Lemma n_1_m_1_ex2 :
forall n m, S (n + 1) = S (m + 1) -> n = m.
Proof.
intros.
info_auto with mydb.
Qed.

Check le_S_n.
Hint Resolve le_S_n : mydb.

Lemma le_S_3 : 
forall n m, S (S (S n)) <= S (S (S m)) -> n <= m.
Proof.
(*intros; do 3 apply le_S_n; assumption.*)
debug auto with mydb.
Qed.

Print le_S_3.

Hint Resolve le_trans : mydb.

Print HintDb mydb.


Lemma le_trans2 :
forall n m p, n<=m -> m<=p -> n<=p.
Proof.
intros.
debug eauto with mydb.
(* tak tez mozna: apply le_trans with m. *)
(* albo tak : 
eapply le_trans.
instantiate (1:=m).
trivial. trivial.
*)
Qed.



Remove Hints le_S_n: mydb.

Print HintDb mydb.

Hint Extern 4 =>
match goal with 
| [ |- _ <= _ ] => simple apply le_S_n
| _ => fail
end : mydb.

Print HintDb mydb.


Lemma le_trans3 :
forall n m p, n<=m -> m<=p -> n<=p.
Proof.
intros.
debug eauto with mydb.
(* tak tez mozna: apply le_trans with m. *)
(* albo tak : 
eapply le_trans.
instantiate (1:=m).
trivial. trivial.
*)
Qed.


(* Hint Rewrite *)

Variable A : Set.
Variable f : A -> A.
Hypothesis rew_f : forall x, f x = f (f x).

(* podpowiedz dla autorewrite; uwaga na nieskonczone ciagi przepisywan *)

Hint Rewrite <- rew_f : mydb.

Print Rewrite HintDb mydb.


Lemma rew_2f :
forall x, f (f x) = f x.
Proof.
intros.
autorewrite with mydb.
reflexivity.
Qed.

(* Hint Rewrite rew_f : mydb.  spowoduje zapetlenie *) 

(* Hint Extern *)

Print HintDb core.

(* podpowiedz dla auto *)
Hint Extern 1 (_ <> _) => discriminate.

Print HintDb core.

Lemma true_false : 
true <> false.
Proof.
info_auto.
Qed.

Hint Extern 1 => 
match goal with
| [ H : S ?m = S ?n |- _ ] => injection H; intro; clear H; try subst
end.

Print HintDb core.

Lemma injection_ex :
forall n m, S (S (S n)) = S (S (S m)) -> n = m.
Proof.
info_auto.
Qed.


(* Hint Unfold *)

Definition idnat (n:nat) : Prop := n = n.

(* podpowiedz dla auto, rozwija definicje w glowie celu *)
Hint Unfold idnat : mydb.

Print HintDb mydb.

Lemma idnat_5 :
idnat 5.
Proof.
auto.
info_auto with mydb.
Qed.


(* predefiniowane bazy *)

Lemma le_r :
forall n m p, n <= m -> n + p <= m + p.
Proof.
info_auto with arith.
Qed.

Print HintDb arith.

(* pattern, omega *)

Require Import Omega.

Lemma mult_distr_1 :
forall n m, n * m + m = (n + 1) * m.
Proof.
intros n m.
(* wybierz podterm (n+1): *)
pattern (n + 1).
(* przepisz tylko w wybranym miejscu: *)
rewrite plus_comm.
simpl.
auto with arith.
Qed.

Print mult_distr_1.

Lemma five_n :
forall n, n + n + n + n + n = 5 * n.
Proof.
intro.
(* wybierz 1. wystapienie n: *)
pattern n at 1.
(* przepisz tylko w wybranym miejscu: *)
rewrite <- mult_1_l.
repeat rewrite mult_distr_1.
auto.
Qed.

Print five_n.

Lemma five_n_omega :
forall n, n + n + n + n + n = 5 * n.
Proof.
intro.
omega.
Qed.

Print five_n_omega.

Fixpoint big_useless_hyp (n:nat) : Prop :=
match n with
| O => n = n
| S m => n = n \/ big_useless_hyp m
end.

Lemma solve_omega :
big_useless_hyp 60 -> 1 <> 0.
Proof.
simpl.
Time omega.
(* Time auto. *)
Qed.

(* programowanie w Ltac *)

Ltac elimcase n := 
generalize (refl_equal n); pattern n at -1; case n; intros.

(* to samo robi istniejaca taktyka: *)
Print Ltac case_eq.
Print Ltac elimcase.
Print Ltac auto.


Lemma cases:
forall (P Q : nat -> Prop) n, 
(n = 0 -> P n) -> (n > 0 -> Q n) -> P n \/ Q n.
Proof.
intros.
elimcase n.
left; subst; intuition.
right; subst; intuition.
Qed.


(* taktyka rekurencyjna : 
   usun wszystkie przeslanki postaci _ = _ *)
Ltac clear_eq_hyp :=
match goal with
| [ H : _ = _ |- _ ] => clear H ; clear_eq_hyp
| _ => idtac
end.

(* inaczej: *)
Ltac clear_eq_hyp' :=
repeat match goal with
       | [ H : _ = _ |- _ ] => clear H
       | _ => idtac
       end.

Lemma clear_eq_hyp :
forall n, 1 = 1 -> 2 = 2 -> 3 = 3 -> 4 = 4 -> 5 = 5 -> 6 = 6 -> 0 <= n.
Proof.
intros.
clear_eq_hyp'.
auto with arith.
Qed.

(* zamien n + m na SSSS...S n *)

Ltac replace_plus :=
repeat match goal with
| [ |- context C [?X + S ?Y] ] => idtac C; rewrite <- plus_n_Sm
| [ |- context [?X + 0] ] => rewrite plus_0_r
| _ => fail
end.

(* stosuj konstruktory le do skutku *)
Ltac apply_le_c := constructor 1 || (constructor 2; apply_le_c).

Lemma le_n_n5 :
forall n, n <= S (n + 4).
Proof.
intro.
replace_plus.
apply_le_c. 
(* info_auto with arith. *)
Qed.


(* sprawdz, czy nie ma juz takiej przeslanki: *)
Ltac not_in_hyps A :=
match goal with
| [ H : A |- _ ] => fail 1
| _ => idtac
end.

(* intros bez powtorzen, 
z wylaczeniem sprawdzania powtorzen przy wprowadzaniu formul *)
Ltac new_intros :=
match goal with
| [ |- ?A -> ?B ] => not_in_hyps A; let h:=fresh "H" in intro h; new_intros 
| [ |- ?A -> ?B ] => let h:=fresh "H" in intro h; clear h; new_intros
| [ |- forall _ : Prop, _ ] => let x:=fresh "A" in intro x; new_intros
| _ => idtac
end.  

Lemma intros_wo_rep :
forall A B:Prop, (forall x:nat,x=0) -> (forall y:nat, y=0) ->
(A -> B) -> (B -> A) -> (A -> B) -> A -> B -> B -> A -> (A -> B) -> B.  
Proof.
new_intros.
assumption.
Qed.

(* inversion *)

(* rozwiaz cel przez n-krotna inwersje: *)
Ltac by_inversion n :=
match n with
| O => idtac "nie udalo sie"
| S ?m => match goal with
         | [ H : _ |- _ ] => solve [inversion H; try subst; idtac H; by_inversion m]
         | _ => idtac n
         end
end.

Tactic Notation "contradiction" "by" "inversion" := by_inversion 1.
Tactic Notation "contradiction" "by" "inversion" constr(n) := by_inversion n.

Lemma not_even_1 :
~ even 5.
Proof.
intro.
contradiction by inversion.
contradiction by inversion 3.
Qed.
 
(* taktyki jako funkcje w Ltac *)

Require Import List.
Import ListNotations.

(* oblicz dlugosc listy *)
Ltac len l :=
match l with
|  _ :: ?ls => let ln := len ls in constr:(S ln)
| [] => O
end.

(* tak nie mozna oczywiscie:
Eval compute in len [2;3].*)

(* ale tak mozna sprawdzic wynik zastosowania taktyki, ktora zwraca wartosc: *)
Goal True.
  let n := len [2;3;4;9] in
    idtac n.
  let l := auto in idtac l.
  let l := constr:(ltac:(constructor):bool) in idtac l.
auto.
Qed.

Definition tail {A} (l:list A) : list A :=
match l with
| [] => ltac:(auto)
| h::t => t
end.

Print tail.

(* len + debugging info *)

Ltac len2 l :=
idtac l;
match l with
|  _ :: ?ls => let ln := len2 ls in constr:(S ln)
| [] => O
end.

Goal True.
  let n := len2 [2;3;4;9] in
    idtac n.
auto.
Qed.

Ltac len3 l k :=
idtac l;
match l with
|  _ :: ?ls => len3 ls ltac:(fun m => k (S m))
| [] => k 0
end.

Goal True.
  len3 [2;3;4;9] ltac:(fun n => pose n).
auto.
Qed.

(* generowanie zmiennych egzystencjalnych *)

(* odraczanie instancjacji kwantyfikatora przez uzycie zmiennej egzystencjalnej *)

Lemma two_gt_one :
(forall x, S x > x) -> 2 > 1.
Proof.
intros.
(* utworzenie nowej zmiennej egzystencjalnej i jej nazwy *)
evar (y : nat).
specialize (H ?y).
(* info_auto. <- tu blad: zostala zmienna niezunifikowana *)
apply H.
Qed.

Print two_gt_one.

(* przyklad z Compcerta *)



Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
   refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _) _)
|| refine (modusponens _ _ (x _ _) _)
|| refine (modusponens _ _ (x _) _).

Lemma mp_test :
forall A B C D E:Prop, (A -> B -> C -> D) -> E.
intros.
exploit H.





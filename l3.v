(*** Zadanie 1 - 1p ***)
(* Rozważmy alternatywną definicję predykatu <= *)

Definition le2 n m := exists k, m = n + k.
(* Definition le2 n m := exists k, m = k + n. *)

(* 1. Udowodnij równoważność le2 i Coqowej definicji le. *)

Lemma lt_impl_le : forall n m : nat, n < m -> n <= m.
Proof.
  intros.
  induction H; apply le_S.
  - apply le_n.
  - assumption.
Qed.

Lemma lt_lower : forall n m:nat, S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - apply lt_impl_le.
    unfold lt.
    assumption.
Qed.

Print le.
Lemma lt_greater : forall m n:nat, n <= m -> S n <= S m.
Proof.
  induction m. intros; induction n.
  * apply le_n.
  * inversion H.
  * intros.
    inversion H.
    - apply le_n.
    - clear m0 H0 H.
      apply IHm in H1.
      apply le_S.
      assumption.
Qed.

Goal forall n m, n <= m -> le2 n m.
Proof.
  intros.
  induction H.
  - unfold le2.
    exists 0. auto.
  - unfold le2; unfold le2 in IHle; destruct IHle.
    exists (S x).
    rewrite H0.
    auto.

  (* other way *)
  (* induction n; intros; unfold le2.
  - exists m; simpl; reflexivity.
  - induction m.
    * inversion H.
    * simpl.
      apply lt_lower in H.
      apply IHn in H; unfold le2 in H; destruct H.
      exists x.
      congruence. *)
Qed.

Lemma zero_lt : forall n, 0 <= n.
Proof.
  induction n.
  - apply le_n.
  - apply le_S; assumption.
Qed.

Goal forall n m, le2 n m -> n <= m.
Proof.
  (* intros.
  unfold le2 in H.
  destruct H.
  induction x.
  - rewrite H.
    simpl.
    apply le_n.
  - apply IHx.
    case x.
    * simpl.
      apply le_n.
    * intros. *)
  induction n; intros; unfold le2 in H; destruct H.
  - apply zero_lt.
  - induction m.
    * inversion H.
    * simpl in H.
      inversion H.
      clear H IHm.
      apply lt_greater.
      unfold le2 in IHn.
      apply IHn.
      exists x; reflexivity.
Qed.

(* 2. Zapisz definicję le2 w sposób równoważny jako predykat definiowany
indukcyjnie. Dowód z punktu 1 powinien być nadal poprawny przy nowej
definicji le2. *)
Print le.
(* Definition le2 n m := exists k, m = n + k. *)
(* k = 0    : le2 n n *)
(* k = k + 1: S m = S (n + k) *)

Inductive le3 (n : nat) : nat -> Prop :=
| le3_n : le3 n n
| le3_S : forall m : nat, le3 n m -> le3 n (S m).

Goal forall n m, n <= m -> le3 n m.
Proof.
  intros.
  induction H.
  - apply le3_n.
  - apply le3_S.
    assumption.
Qed.

Goal forall n m, le3 n m -> n <= m.
Proof.
  intros.
  induction H.
  - apply le_n.
  - apply le_S.
    assumption.
Qed.

(*** Zadanie 2 - 4p ***)
(* Rozważmy zasadę indukcji noetherowskiej na zbiorze liczb
naturalnych z porządkiem <= *)

Hypothesis IH : forall (P : nat -> Prop) m, (forall n, n < m -> P n) -> P m.

Lemma P0 : forall P : nat -> Prop, P 0.
Proof.
  intros.
  apply IH.
  intros.
  inversion H.
Qed.

Lemma le_weaker : forall n m, S n <= m -> n <= m.
Proof.
  intros.
  induction H.
  - apply le_S. apply le_n.
  - apply le_S. assumption.
Qed.

Lemma le_trans : forall a b, a <= b -> forall c, b <= c -> a <= c.
Proof.
  intros a b H.
  induction H.
  - intros. assumption.
  - intros. induction H0.
    * apply le_S. assumption.
    * apply IHle.
      apply le_S.
      apply le_weaker.
      assumption.
Qed.

Theorem strong_induction:
  forall P : nat -> Prop,
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
  intros.
  apply H.
  induction n.
  - intros. inversion H0.
  - induction m; intros. 
    * apply H. intros. inversion H1.
    * apply H. 
      unfold lt in *.
      intros.
      apply IHn.
      apply lt_lower in H0.
      clear H IHn IHm P.
      apply le_trans with (b := S m); assumption.
Qed.

(* Goal forall P : nat -> Prop,
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
  intros. apply nat_ind.
  - apply H. intros. inversion H0.
  - intros.
    apply nat_ind.
    * apply H. intros. inversion H1.
    * intros.
      apply H.
      intros.
      unfold lt in *.
Qed. *)

Print nat_ind.

(* Udowodnij tę zasadę korzystając z indukcji matematycznej (tzn. z
twierdzenia nat_ind). [Uwaga: trzeba wzmocnić hipotezę indukcyjną.] *)

(*** Zadanie 3 - 3p [+ 5p*] ***)
(* 1. Zdefiniuj funkcję fib : nat -> nat wyznaczającą kolejne liczby
Fibonacciego wprost z definicji:

F_0 = 0 
F_1 = 1 
F_n = F_(n-1) + F_(n-2) *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => 
    match n' with
    | 0 => 1
    | S n'' => fib n' + fib n''
    end
  end.

(* 2. Udowodnij cel *)

Require Import Arith.

Lemma le_add : forall n m, 1 <= n -> 1 <= m -> 2 <= n + m.
Proof.
  intros.
  induction H; cbn.
  - apply lt_greater. assumption.
  - apply le_S. assumption.
Qed.

Goal forall n, n > 0 -> fib n > 0.
Proof.
  unfold gt in *.
  unfold lt in *.
  intros.
  induction n using strong_induction.
  induction H; cbn.
  * apply le_n.
  * induction H.
    + cbn. apply le_n.
    + assert (1 <= fib m /\ 1 <= fib (S m)). split.
      - apply H0.
        unfold lt. apply le_S. apply le_n.
        assumption.
      - apply H0.
          unfold lt. apply le_n.
          apply le_S. assumption.
      - destruct H1.
        assert (2 <= fib (S m) + fib m).
        apply le_add; assumption.
        auto with arith.
Qed.

(* Jakiej zasady indukcji potrzebujesz?

3*. Udowodnij następującą własność liczb Fibonacciego: Jeśli n jest
podzielne przez 3, to fib n jest liczbą parzystą, a jeśli n nie jest
podzielne przez 3, to fib n jest liczbą nieparzystą. [Zdefiniuj
predykaty parzystości i nieparzystości wzajemnie indukcyjnie.]

4*. Zdefiniuj i udowodnij zasadę indukcji odzwierciedlającą schemat
wywołań rekurencyjnych funkcji Fibonacciego. Użyj jej do udowodnienia
twierdzenia z punktu 2.

 *)

(*** Zadanie 4 - 3p ***)
(*

1. Zdefiniuj indukcyjny predykat sub taki, że sub l1 l2 zachodzi wtw
gdy l1 jest podlistą l2
(tj. l1 zawiera pewien podciąg elementów l2). *)

(* 2. Udowodnij, że wynik działania funkcji filter jest podlistą
argumentu tej funkcji: *)

Require Import List.

Inductive sub (A : Type) : list A -> list A -> Prop := 
| sub_n : forall xs, sub A xs xs
| sub_c : forall x xs ys, sub A xs ys -> sub A (x :: xs) (x :: ys)
| sub_s : forall x xs ys, sub A xs ys -> sub A       xs  (x :: ys).

Print filter.

Lemma filter_sublist:
(* forall (A : Type) (f : A -> bool) l1 l2, l2 = filter f l1 -> sub A l2 l1. *)
forall (A : Type) (f : A -> bool) l, sub A (filter f l) l.
Proof.
  intros.
  induction l.
  - cbn. apply sub_n.
  - cbn.
    case (f a).
    + apply sub_c. assumption.
    + apply sub_s. assumption.
Qed.

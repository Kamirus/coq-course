Require Import Arith.
Require Import Peano.

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

Lemma le_lower : forall m n, S n <= S m -> n <= m.
Proof.
  (* auto with arith. *)
  intros.
  inversion H.
  - apply le_n.
  - apply lt_impl_le.
    unfold lt.
    assumption.
Qed.

Lemma le_greater : forall m n:nat, n <= m -> S n <= S m.
Proof.
  (* auto with arith. *)
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
Qed.

Lemma le_to_le2 : forall n m, n <= m -> le2 n m.
Proof.
  induction n; intros; unfold le2.
  - exists m; simpl; reflexivity.
  - induction m.
    * inversion H.
    * simpl.
      apply le_lower in H.
      apply IHn in H; unfold le2 in H; destruct H.
      exists x.
      congruence.
Qed.

Lemma zero_lt : forall n, 0 <= n.
Proof.
  induction n.
  - apply le_n.
  - apply le_S; assumption.
Qed.

Lemma le2_to_le : forall n m, le2 n m -> n <= m.
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
      apply le_greater.
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

Inductive le3 (n m k : nat) : Prop :=
| le3c : m = n + k -> le3 n m k.
(* Inductive le3 (n m k : nat) : Prop -> Prop :=
| le3c : le3 n m k (m = n + k). *)

(* Goal forall n m, le2 n m -> exists k, le3 n m k (m = n + k). *)
Goal forall n m, le2 n m -> exists k, le3 n m k.
Proof.
  intros.
  unfold le2 in *. destruct H.
  exists x.
  apply le3c.
  assumption.
Qed.

(* Goal forall n m k, le3 n m k (m = n + k) -> n <= m. *)
Goal forall n m k, le3 n m k -> n <= m.
Proof.
  induction n; intros; unfold le2 in H; destruct H.
  - apply zero_lt.
  - induction m.
    * inversion H.
    * simpl in H.
      inversion H.
      clear H IHm.
      apply le_greater.
      unfold le2 in IHn.
      auto with arith.
Qed.

(*** Zadanie 2 - 4p ***)
(* Rozważmy zasadę indukcji noetherowskiej na zbiorze liczb
naturalnych z porządkiem <= *)

Lemma le_weaker : forall n m, S n <= m -> n <= m.
Proof.
  intros.
  induction H.
  - apply le_S. apply le_n.
  - apply le_S. assumption.
Qed.

Lemma le_trans : forall a b, a <= b -> forall c, b <= c -> a <= c.
Proof.
  induction a, b; intros.
  assumption.
  auto with arith.
  inversion H.
  apply le_to_le2 in H. apply le_to_le2 in H0.
  apply le2_to_le.
  unfold le2 in *.
  destruct H. destruct H0.
  exists (x + x0).
  rewrite H in H0.
  rewrite H0.
  auto with arith.
Qed.

SearchPattern (_ + _ = _ + _).

Lemma le_trans' : forall a b, a <= b -> forall c, b <= c -> a <= c.
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
      apply le_lower in H0.
      clear H IHn IHm P.
      apply le_trans with (b := S m); assumption.
Qed.

Goal forall P : nat -> Prop,
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
  intros P Hind.
  cut (forall n m, m <= n -> P m).
  - intros. apply (H n n). apply le_n.
  - induction n; intros.
    * inversion H.
      apply Hind.
      intros.
      inversion H1.
    * unfold lt in *.
      inversion H. (* <- key*)
      apply Hind.
      + intros. apply IHn. apply le_lower. assumption.
      + apply IHn. assumption. 
      (* apply Hind. intros.
      apply IHn.
      clear P Hind IHn.
      apply le_lower.
      apply le_trans with (b := m); assumption. *)
Qed.

(* stronger in Goal, same problem with le trans *)
(* Goal forall P : nat -> Prop,
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n /\ (forall m, m < n -> P m).
Proof.
  intros P Hind.
  induction n.
  - split. apply Hind.
    * intros. inversion H.
    * intros. apply Hind. inversion H.
  - destruct IHn as [H Hn]. split.
    * apply Hind.
      induction m; intros.
      + apply Hind. intros. inversion H1.
      + intros. 
        apply Hind. intros.
Qed. *)

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

Lemma le_add : forall n m, 1 <= n -> 1 <= m -> 2 <= n + m.
Proof.
  intros.
  induction H; cbn.
  - apply le_greater. assumption.
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

(* Jakiej zasady indukcji potrzebujesz? *)

(* 3*. Udowodnij następującą własność liczb Fibonacciego: Jeśli n jest
podzielne przez 3, to fib n jest liczbą parzystą, a jeśli n nie jest
podzielne przez 3, to fib n jest liczbą nieparzystą. [Zdefiniuj
predykaty parzystości i nieparzystości wzajemnie indukcyjnie.] *)

Inductive even : nat -> Prop :=
| even0 : even 0
| evenc : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
| odd1 : odd 1
| oddc : forall n, even n -> odd (S n).

(* Definition div3 n := exists k, n = 3 * k. *)
Inductive div3 : nat -> Prop :=
| div30 : div3 0
| div3c : forall n, div3 n -> div3 (S (S (S n))).

Lemma fib3 : forall n, fib (S (S (S n))) = fib (S n) + fib n + fib (S n).
Proof.
  auto.
Qed.

Lemma even2 : forall n, even (2 * n).
Proof.
  induction n.
  - cbn. apply even0.
  - 
    assert (2 * n = n + n). cbn. auto with arith.
    assert (2 * S n = 2 + 2 * n). cbn. auto with arith.
    rewrite H0.
    apply evenc.
    apply oddc.
    assumption.
Qed.

(* how to *)
(* Lemma even_to : forall n, even n -> exists k, n = 2 * k.
Proof.
  intros.
  induction H.
  

  induction n; intros.
  - exists 0. cbn. reflexivity.
  - apply oddc in H.
    + exists 1. cbn. reflexivity.
Qed. *)

Lemma even_aux : forall n, even n -> forall m, even (n + 2 * m).
Proof.
  intros n H.
  induction m.
  - intros. cbn. rewrite <- plus_n_O. assumption.
  - 
    assert (2 * S m = 2 + 2 * m).
    rewrite <- mult_n_Sm.
    auto with arith.

    apply oddc in IHm. apply evenc in IHm.
    rewrite H0.
    cbn. cbn in IHm.
    rewrite plus_n_Sm in IHm.
    rewrite plus_n_Sm in IHm.
    assumption.
Qed.

Lemma aba_eq_b2a : forall a b, a + b + a = b + 2 * a.
Proof.
  intros.
  cbn.
  rewrite plus_comm with (n := b) (m := (a + (a + 0))).
  rewrite <- plus_n_O.
  rewrite plus_comm.
  apply plus_assoc.
Qed.

Goal forall n, div3 n -> even (fib n).
Proof.
  intros.
  induction H.
  - cbn. apply even0.
  - rewrite fib3. simpl (fib (S (S n))).
    assert (fib (S n) + fib n + fib (S n) = fib n + 2 * fib (S n)).
    apply aba_eq_b2a.
    rewrite H0.
    apply even_aux.
    assumption.
Qed.

(* Definition ndiv3 n : nat -> Prop := n = exists k r, 3 * k + r /\ r <= 2. *)

(* mod3 n r  n mod 3 = r *)
(* Definition mod3 n r := n mod 3 = r. *)
Inductive mod3 : nat -> nat -> Prop :=
| mod300 : mod3 0 0
| mod30s : forall n, mod3 n 2 -> mod3 (S n) 0
| mod31s : forall n, mod3 n 0 -> mod3 (S n) 1
| mod32s : forall n, mod3 n 1 -> mod3 (S n) 2.

Lemma unfold_mod3 : forall n r, mod3 n r -> exists k, n = 3 * k + r /\ r <= 2.
Proof.
  intros. induction H.
  - exists 0. auto.
  - destruct IHmod3. destruct H0. rewrite H0.
    exists (S x). split. 
    rewrite <- mult_n_Sm.
    rewrite plus_n_Sm.
    auto. auto.
  - destruct IHmod3. destruct H0. rewrite H0.
    exists x. split. auto with arith. auto.
  - destruct IHmod3. destruct H0. rewrite H0.
    exists x. split. auto with arith. auto.
Qed.

Goal forall n, mod3 n 1 -> odd (fib n).
Proof.
  intros. inversion H.
  induction H.
  - inversion H1.
  - injection H1. intros.
    apply unfold_mod3 in H0. apply unfold_mod3 in H.
    destruct H0. destruct H.
    destruct H. destruct H0.
    rewrite H2 in *. contradiction.
Qed.

(* 4*. Zdefiniuj i udowodnij zasadę indukcji odzwierciedlającą schemat
wywołań rekurencyjnych funkcji Fibonacciego. Użyj jej do udowodnienia
twierdzenia z punktu 2. *)

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

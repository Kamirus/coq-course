Require Import PeanoNat.

(*** Zadanie 1 - 3p *)
(* Rozważmy typ list indeksowanych długością *)

Inductive llist {A:Type} : nat -> Type := 
| lnil : llist 0 
| lcons : forall n, A -> llist n -> llist (S n).

(* 1. Zdefiniuj funkcję konwersji zwykłych list do typu llist oraz vice versa: *)

Require Import List.

Fixpoint inject (A : Type) (ls : list A) : llist (length ls) :=
  match ls with
  | nil => lnil
  | x :: xs => lcons _ x (inject A xs)
  end.

Require Program.

Obligation Tactic := eauto.

Program Fixpoint unject (A : Type) (n : nat) : llist n -> list A :=
  match n with
  | 0 => fun _ => nil
  | S n => fun ll =>
    match ll with
    | lnil => False_rect _ _
    | lcons _ x xs => cons x (unject A n xs)
    end
  end.
Obligations.
Obligation 1.
intros A n0 n H1 ll H H2. inversion H.
  Qed.

Search (forall xs xs' x, xs = xs' -> x :: xs = x :: xs').

(* 2. Udowodnij, że złożenie unject o inject jest identycznością. *)
Lemma un_o_in_id : forall A l, unject A (length l) (inject A l) = l.
Proof.
  intros.
  induction l; cbn; auto.
  rewrite IHl.
  reflexivity.
  Qed.

(* 3. Udowodnij, że złożenie inject o unject jest identycznością.
Tej własności nie da się zapisać wprost w Coqu - w tym przypadku powstaje 
problem z typowaniem równości inject (unject ls) = ls *)

(* Rozwiąż ten problem na dwa sposoby: *)
(* a. *)
(* Zdefiniuj własny typ równości na listach llist_eq,  *)

Inductive llist_eq {A : Type} : forall n m, @llist A n -> @llist A m -> Prop :=
| eq_nil  : llist_eq 0 0 lnil lnil
| eq_cons : forall n m x xs ys, n = m ->
  llist_eq n m xs ys -> llist_eq (S n) (S m) (lcons n x xs) (lcons m x ys).

(* udowodnij, że jest to relacja równoważności; *)

Goal forall A n l, @llist_eq A n n l l.
Proof.
  intros.
  induction l.
  - apply eq_nil.
  - apply eq_cons; auto.
  Qed.

Goal forall A n m xs ys, @llist_eq A n m xs ys -> @llist_eq A m n ys xs.
Proof.
  intros.
  induction H.
  - apply eq_nil.
  - apply eq_cons; auto.
  Qed.

Require Import Program.Equality.

Goal forall A n m xs ys, @llist_eq A n m xs ys -> forall k zs, @llist_eq A m k ys zs -> @llist_eq A n k xs zs.
Proof.
  intros A n m xs ys H.
  induction H; intros; auto.
  inversion H1. clear H1. subst.
  simpl_existTs.
  subst.
  apply eq_cons; auto.
  Qed.

Lemma length_unject : forall A n l, length (unject A n l) = n.
Proof.
  intros.
  induction l; cbn; auto.
Defined.

(* udowodnij, że dla wszystkich list zachodzi llist_eq (inject (unject ls)) ls *)
Goal forall A n l, llist_eq (length (unject A n l)) n (inject A (unject A n l)) l.
Proof.
  intros.
  induction l; cbn.
  - apply eq_nil.
  - apply eq_cons; auto.
    apply length_unject.
  Qed.

(* b. Zdefiniuj funkcję, która wykonuje koercję elementów typu llist n do typu 
  llist (length (unject ls)) i wykorzystaj ją do sformułowania lematu. *)
Fixpoint llcoerce {A : Type} (n : nat) (l : @llist A n) : 
  @llist A (length (unject A n l)) :=
  match l with
  | lnil => lnil
  | lcons n x xs => lcons _ x (llcoerce n xs)
  end.

Lemma in_o_un_id : forall A n l, inject A (unject A n l) = llcoerce n l.
Proof.
  intros. induction l; cbn; auto.
  rewrite IHl. reflexivity.
  Qed.

(*** Zadanie 2 - 6p *)

(* 1. Zdefiniuj predykat [sorted] spełniony dla list posortowanych rosnąco. *)

Inductive sorted : list nat -> Prop :=
| sorted_nil  : sorted nil
| sorted_one  : forall n : nat, sorted (cons n nil)
| sorted_cons : forall x xs n, n <= x -> sorted (cons x xs) -> sorted (n :: x :: xs).

(* 2. Napisz funkcję sortowania przez wstawianie o następującej specyfikacji: *)

Require Import Permutation.

Print Permutation.
Search (forall x, Permutation x x).
(* Inductive Permutation (A : Type) : list A ⟶ list A ⟶ Prop ≜
    perm_nil : Permutation nil nil
  | perm_skip : ∀ (x : A) (l l' : list A),
                Permutation l l' ⟶ Permutation (x :: l) (x :: l')
  | perm_swap : ∀ (x y : A) (l : list A),
                Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : ∀ l l' l'' : list A,
                 Permutation l l' ⟶ Permutation l' l'' ⟶ Permutation l l'' *)

Search ((~ (_ <= _)) = _ > _).

Search (_ <= _ \/ _ < _).
Search (forall a b, {a <= b} + {a > b}).
Search (Permutation (_ :: nil) (_ :: _) -> _).

Lemma is_le (a b : nat) : {a <= b} + {a > b}.
Proof.
  apply Compare_dec.le_gt_dec.
  (* assert (a <= b \/ b < a).
  apply Nat.le_gt_cases.
  destruct H.

  decide equality.
  assert (a > b = ~ (a <= b)).
  
  unfold gt.
  change ({a <= b} + {~ (a <= b)}). *)
  Qed.

Lemma sort_impl_hd_le : forall xs x a, sorted (x :: xs) -> In a xs -> x <= a.
Proof.
  induction xs; intros.
  - cbn in H0. inversion H0.
  - cbn in H0. destruct H0; subst.
    + inversion H. subst. assumption.
    + apply IHxs.
      inversion H. clear H. subst. 
      inversion H5. clear H5. subst.
      inversion H0. subst.
      apply sorted_cons; auto. apply Nat.le_trans with (m := a); auto.
      assumption.
  Qed.

Lemma perm_in : forall {A : Type} l x xs, @Permutation A l (x :: xs) -> In x l.
Proof.
  intros.
  dependent induction H.
  - cbn. auto.
  - cbn. auto.
  - assert (x :: xs = x :: xs). auto.
    apply IHPermutation2 in H1.
    apply Permutation_sym in H.
    apply Permutation_in with (l := l'); auto.
  Qed.

Lemma ins_aux : forall x xs 
  , sorted (x :: xs)
  -> forall n a l, sorted (a :: l)
  -> x < n
  -> Permutation (n :: xs) (a :: l)
  -> x <= a.
Proof.
  intros.
  apply perm_in in H2. cbn in H2. destruct H2.
  - rewrite <- H2. auto with arith.
  - apply sort_impl_hd_le with (xs := xs); auto.
  Qed.

Definition insert : forall (n : nat) (l : list nat) (s : sorted l),
  {l' : list nat | Permutation (n :: l) l' /\ sorted l'}.
  refine (
    fix ins (n : nat) (l : list nat) : 
      sorted l -> {l' : list nat | Permutation (n :: l) l' /\ sorted l'} :=
      match l with
      | nil => fun s => exist _ (n :: nil) _
      | x :: xs => fun s =>
        match is_le n x with
        | left  n_le_x => exist _ (n :: x :: xs) _
        | right x_gt_n => 
          match ins n xs _ with
          | exist _ nxs p => exist _ (x :: nxs) _
          end
        end  
      end
  ).
  - split. apply perm_skip. apply perm_nil. apply sorted_one.
  - split. apply Permutation_refl. apply sorted_cons; auto.
  - inversion s. clear s. subst. apply sorted_nil. assumption.
  - split; cbn in p; destruct p.
    + assert (Permutation (n :: x :: xs) (x :: n :: xs)).
      apply perm_swap. apply perm_skip with (x := x) in H.
      apply perm_trans with (l' := x :: n :: xs); assumption.
    + induction nxs.
      * apply sorted_one.
      * apply sorted_cons.
        apply ins_aux with (xs := xs) (n := n) (l := nxs); auto.
        auto.
Defined.

Lemma snd : forall P Q, P /\ Q -> Q.
Proof.
  intros. destruct H. assumption.
Defined.


(* Definition insertion_sort (l : list nat) : {l' : list nat | Permutation l l' /\ sorted l'}.
refine (
  fix ins_sort (l : list nat) : {l' : list nat | Permutation l l' /\ sorted l'} :=
    match l return {l' : list nat | Permutation l l' /\ sorted l'} with
    | nil => exist _ nil _
    | cons x xs =>
      match ins_sort xs as f return {l' : list nat | Permutation (x :: proj1_sig f) l' /\ sorted l'} with
      | exist _ xs' p => insert x xs' (fst p)
      end
    end
). *)

Fixpoint ins (n : nat) (l : list nat) :=
  match l with
  | nil => cons n nil
  | cons x xs => 
    match is_le n x with
    | left  n_le_x => n :: l
    | right n_gt_x => x :: ins n xs
    end
  end.

Fixpoint ins_sort (l : list nat) :=
  match l with
  | nil => nil
  | x :: xs => ins x (ins_sort xs)
  end.

Lemma perm_ins : forall n l, Permutation (n :: l) (ins n l).
Proof.
  intros. induction l.
  - cbn. auto.
  - cbn.
    induction (is_le n a); auto.
    assert (Permutation (n :: a :: l) (a :: n :: l)). apply perm_swap.
    assert (Permutation (a :: n :: l) (a :: ins n l)). apply perm_skip; auto.
    apply perm_trans with (l' := a :: n :: l); auto.
  Qed.

Lemma perm_ins_sort : forall l, Permutation l (ins_sort l).
Proof.
  induction l; cbn; auto.
  assert (Permutation (a :: ins_sort l) (ins a (ins_sort l))). apply perm_ins.
  apply perm_skip with (x := a) in IHl.
  apply perm_trans with (l' := a :: ins_sort l); auto.
  Qed.

Lemma sorted_uncons : forall a l, sorted (a :: l) -> sorted l.
Proof.
  intros. inversion H; subst; auto. apply sorted_nil.
  Qed.

Lemma sorted_ins : forall x l, sorted l -> sorted (ins x l).
Proof.
  intros. induction l; cbn.
  - apply sorted_one.
  - induction (is_le x a).
    + apply sorted_cons; auto.
    + apply sorted_uncons in H as H0. apply IHl in H0. clear IHl.
      assert (Permutation (x :: l) (ins x l)). apply perm_ins.
      induction (ins x l).
      * apply sorted_one.
      * apply sorted_cons; auto.
        apply ins_aux with (xs := l) (a := a0) (l := l0) (x := a) (n := x); auto.
  Qed.

Lemma sorted_ins_sort : forall l, sorted (ins_sort l).
Proof.
  induction l; cbn.
  apply sorted_nil.
  apply sorted_ins. assumption.
  Qed.

Definition insertion_sort (l : list nat) : 
  {l' : list nat | Permutation l l' /\ sorted l'} :=
  exist _ (ins_sort l) (conj (perm_ins_sort l) (sorted_ins_sort l)).

(*** Zadanie 3 - 8p *)

(* Rozwiąż poprzednie zadanie używając typu danych sorted_list indeksowanych
typem option nat takich, że sorted_list None reprezentuje listę pustą,
a sorted_list (Some n) jest typem list posortowanych rosnąco,
których najmniejszym elementem jest n. *)

(* 1. Zdefiniuj tak określony indukcyjny typ danych sorted_list. *)

(* 2. Napisz funkcję insert, która wstawia element do sorted_list. *)

(* 3. Dowolną listę posortowaną rosnąco określa para złożona z indeksu x i listy
typu sorted_list x. Napisz specyfikację funkcji insertion_sort przy użyciu tego
typu oraz zdefiniuj tę funkcję. *)

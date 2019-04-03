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
  end
.
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
Obligation 1. intros A n0 n H1 ll H H2. inversion H. Qed.

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

Hint Constructors llist_eq.

(* udowodnij, że jest to relacja równoważności; *)

Goal forall A n l, @llist_eq A n n l l.
Proof.
  intros. induction l; auto.
  (* - apply eq_nil.
  - apply eq_cons; auto. *)
  Qed.

Goal forall A n m xs ys, @llist_eq A n m xs ys -> @llist_eq A m n ys xs.
Proof.
  intros. induction H; auto.
  (* - apply eq_nil.
  - apply eq_cons; auto. *)
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
  intros. induction l; cbn; auto.
  Qed.

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
  end
.
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
  - assert (x :: xs = x :: xs). auto. apply IHPermutation2 in H1.
    (* ^ jak zrobić bez assert? *)
    apply Permutation_sym in H.
    apply Permutation_in with (l := l'); auto.
  Qed.

Fixpoint ins (n : nat) (l : list nat) :=
  match l with
  | nil => cons n nil
  | cons x xs => 
    match is_le n x with
    | left  n_le_x => n :: l
    | right n_gt_x => x :: ins n xs
    end
  end
.
Fixpoint ins_sort (l : list nat) :=
  match l with
  | nil => nil
  | x :: xs => ins x (ins_sort xs)
  end
.
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
        clear IHl0.
        (* Permutation (x :: l) (a0 :: l0) *)
        apply perm_in with (xs := l0) in H1. (* więc a0 in x :: l *)
        cbn in H1. destruct H1. (* a0 = x \/ a0 in l *)
        { (* a <= x = a0 *) rewrite <- H1. auto with arith. }
        { (* a <= list l  /\  a0 in l  ->  a <= a0 *) 
          apply sort_impl_hd_le with (xs := l); assumption.
        }
  Qed.

Lemma sorted_ins_sort : forall l, sorted (ins_sort l).
Proof.
  induction l; cbn.
  apply sorted_nil.
  apply sorted_ins. assumption.
  Qed.

Definition insertion_sort (l : list nat) : 
  {l' : list nat | Permutation l l' /\ sorted l'} :=
  exist _ (ins_sort l) (conj (perm_ins_sort l) (sorted_ins_sort l))
.
(*** Zadanie 3 - 8p *)

(* Rozwiąż poprzednie zadanie używając typu danych sorted_list indeksowanych
typem option nat takich, że sorted_list None reprezentuje listę pustą,
a sorted_list (Some n) jest typem list posortowanych rosnąco,
których najmniejszym elementem jest n. *)

(* 1. Zdefiniuj tak określony indukcyjny typ danych sorted_list. *)
Inductive lift_le : nat -> option nat -> Prop :=
| le_none : forall n, lift_le n None
| le_some : forall n m, n <= m -> lift_le n (Some m)
.
Inductive sorted_list : option nat -> Set :=
| sort_nil  : sorted_list None
| sort_cons : forall x m, lift_le x m -> sorted_list m -> sorted_list (Some x)
.
Require Import Coq.Init.Datatypes.

Definition min' (n : nat) (m : option nat) : option nat :=
  match m with
  | None => Some n
  | Some m => Some (min n m)
  end
.
(* 2. Napisz funkcję insert, która wstawia element do sorted_list. *)
Program Fixpoint insert m n (l : sorted_list m) : sorted_list (min' n m) :=
  match l with
  | sort_nil => sort_cons n None (le_none n) sort_nil
  | sort_cons x m lift_le_x_m xs => 
    match is_le n x with
    | left  n_le_x => sort_cons n (Some x) (le_some n x n_le_x) l
    | right n_gt_x => sort_cons x _ _ (insert _ n xs)
    end
  end
.
Obligations.
Next Obligation. intros. subst. cbn. rewrite min_l; auto. Qed.
Next Obligation. 
  intros. subst.
  unfold gt in n_gt_x. rename n_gt_x into p. clear Heq_anonymous. apply Nat.lt_le_incl in p.
  inversion lift_le_x_m; subst; cbn; auto.
  apply le_some; auto.
  apply le_some.
  apply Nat.min_glb; auto.
  Qed.

Next Obligation. 
  intros. subst. cbn. 
  assert (min n x = x).
  unfold gt in n_gt_x. clear Heq_anonymous. apply Nat.lt_le_incl in n_gt_x.
  apply Nat.min_r; auto.
  rewrite H. reflexivity.
  Qed.

(* 3. Dowolną listę posortowaną rosnąco określa para złożona z indeksu x i listy
typu sorted_list x. Napisz specyfikację funkcji insertion_sort przy użyciu tego
typu oraz zdefiniuj tę funkcję. *)

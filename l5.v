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
Definition llcoerce {A : Type} (n : nat) (l : @llist A n) : 
  @llist A (length (unject A n l)).
rewrite length_unject.
refine (l).
Defined.

Lemma in_o_un_id : forall A n l, inject A (unject A n l) = llcoerce n l.
Proof.
  intros. induction l; cbn; auto.
  - rewrite IHl. unfold llcoerce.
Qed.

(*** Zadanie 2 - 6p *)

(* 1. Zdefiniuj predykat [sorted] spełniony dla list posortowanych rosnąco. *)

(* sorted : list nat -> Prop *)

(* 2. Napisz funkcję sortowania przez wstawianie o następującej specyfikacji: *)

Require Import Permutation.

(* Definition insertion_sort : forall l : list nat, 
  {l' : list nat | Permutation l l' /\ sorted l'}. *)

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

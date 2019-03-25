Require Import PeanoNat.
Require Import Arith.
Require Import List.

(*** Zadanie 1 - 4p *)

(* Struktury algebraiczne możemy wygodnie reprezentować w Coqu za
pomocą rekordów zależnych, których pola opisują własności definiujące
daną strukturę. *)

(* 1. Zapoznaj się z komendą Record. *)

(* 2. Zdefiniuj typ monoidu jako rekord zależny, zawierający odpowiednie
pola, w tym łączność operacji i obustronną neutralność wyróżnionego
elementu. *)
Record Monoid {A:Type} (dot : A -> A -> A) (empty : A) : Prop := mkMonoid
  { dot_assoc : forall a b c, dot a (dot b c) = dot (dot a b) c
  ; empty_r : forall a, dot a empty = a
  ; empty_l : forall a, dot empty a = a
  }.

(* 3. Udowodnij, że w każdym monoidzie istnieje dokładnie jeden element
neutralny. *)
Goal forall (A:Type) (dot : A -> A -> A) (e : A) (e' : A),
  Monoid dot e -> Monoid dot e' -> e = e'.
Proof.
  intros.
  (* e = dot e e' = e' *)
  assert (dot e e' = e).
  apply empty_r. assumption.
  rewrite <- H1.
  apply empty_l. assumption.
Qed.

(* 4. Zdefiniuj w Coqu pojęcie homomorfizmu między monoidami. *)
(* Record Homomorphism {A B: Type} (f : A -> B) := mkHomomorphism
  { homomorph : forall dot dot' e e', Monoid dot e -> Monoid dot' e' -> 
      forall a b, f (dot a b) = dot' (f a) (f b)
  }. *)
Record Homomorphism {A B: Type} 
  {dot: A -> A -> A} {e : A} {dot' : B -> B -> B} {e' : B}
  (f : A -> B)
  (* (dot : A -> A -> A) (e : A) (dot' : B -> B -> B) (e' : B) *)
  (m1 : Monoid dot e) (m2 : Monoid dot' e') := mkHomomorphism
    { homomorph : forall a b, f (dot a b) = dot' (f a) (f b)
    }.

(* 5. Podaj dwa przykłady monoidów i zainstaluj je w typie monoid. Napisz
funkcję pomiędzy nośnikami tych monoidów, która definiuje homomorfizm
pomiędzy nimi. Udowodnij, że jest to homomorfizm. *)

(* Search (_ + (_ + _) = _ + _ + _).
Search (_ + 0).
Search (0 + _).
Search (forall a b c, a + (b + c) = a + b + c).
SearchHead (Nat.add_assoc). *)

Definition mono_add := 
  mkMonoid nat Nat.add 0 Nat.add_assoc Nat.add_0_r Nat.add_0_l.

Import ListNotations.

Definition app_unit (xs : list unit) (ys : list unit) : list unit :=
  app xs ys.

Lemma app_assoc_unit : forall a b c,
  app_unit a (app_unit b c) = app_unit (app_unit a b) c.
Proof.
  intros. unfold app_unit. apply app_assoc.
Qed.

Lemma app_nil_l_unit : forall a, app_unit [] a = a.
Proof.
  intros. unfold app_unit. apply app_nil_l.
Qed.

Lemma app_nil_r_unit : forall a, app_unit a [] = a.
Proof.
  intros. unfold app_unit. apply app_nil_r.
Qed.

Definition mono_list :=
  mkMonoid (list unit) app_unit [] app_assoc_unit app_nil_r_unit app_nil_l_unit.

Fixpoint nat_to_list (n : nat) : list unit :=
  match n with
  | 0 => []
  | S n => tt :: (nat_to_list n)
  end.

Lemma homomorph_nat_to_list :
  forall a b, nat_to_list (a + b) = app_unit (nat_to_list a) (nat_to_list b).
Proof.
  intros.
  unfold app_unit.
  induction a.
  - cbn. reflexivity.
  - cbn. rewrite IHa. reflexivity.
Qed.

Definition hom_nat_to_list := 
  mkHomomorphism nat (list unit) Nat.add 0 app_unit []
    nat_to_list mono_add mono_list homomorph_nat_to_list.

(* 6. Record jest cukrem syntaktycznym. W jaki sposób za pomocą znanych
konstrukcji Coqa możemy inaczej zdefiniować typ monoid? *)

Inductive monoid' {A:Type} (dot : A -> A -> A) (empty : A) : Prop :=
| mkMonoid' :
    forall a b c, dot a (dot b c) = dot (dot a b) c ->
    forall a, dot a empty = a ->
    forall a, dot empty a = a ->
    monoid' dot empty.


(* -------------------------------------------------------------------------- *)


(*** Zadanie 2 - 4p + 10p *)

(* 1. Zdefiniuj indukcyjny typ danych reprezentujący drzewa
czerwono-czarne  *)
Inductive color := black | red.

Inductive rbtree (A : Set) : color -> nat -> Set :=
| rb_e : rbtree A black 0
| rb_r : forall h, rbtree A black h -> A -> rbtree A black h -> rbtree A red h
| rb_b : forall h c c', rbtree A c h -> A -> rbtree A c' h -> rbtree A black (S h).

(* taki, że typ rbtree A c h reprezentuje drzewa zawierające elementy
typu A, których korzeń ma kolor c i głębokość czarnych węzłów h. *)

(* 2. Zdefiniuj funkcję  *)
(* Fixpoint depth {A : Set} {c : color} {n : nat} *)
Fixpoint depth {A : Set} {c : color} {n : nat}
    (cmp : nat -> nat -> nat) (t : rbtree A c n) : nat :=
  match t with
  | rb_e _ => 0
  | rb_r _ h tl _ tr => S (cmp (depth cmp tl) (depth cmp tr))
  | rb_b _ _ _ _ tl _ tr => S (cmp (depth cmp tl) (depth cmp tr))
  end.

(* pozwalającą obliczyć maksymalną i minimalną głębokość drzewa, w
zależności od tego, jaką funkcję podamy jako argument. *)

Require Import Coq.Structures.GenericMinMax.

SearchPattern (_ <= _ -> S _ <= S _).

(* 3. Udowodnij własności  *)
Goal forall A c n (t : rbtree A c n), depth min t >= n.
Proof.
  intros.
  induction t; cbn; unfold ge in *; auto.
  - apply le_S. apply Nat.min_glb_iff. split; assumption.
  - apply le_n_S. apply Nat.min_glb_iff. split; assumption.
Qed.

Search (forall n m, n*m = m*n).
Search (forall n, n + 1 = S n).
Search (forall a b c, a + (b + c) = (a + b) + c).
Check Nat.add_assoc.

Lemma depth_max' : forall A c n (t : rbtree A c n),
  match c with
    | red => depth max t <= 2 * n + 1
    | black => depth max t <= 2 * n
  end.
Proof.
  intros.

  assert (forall h, 2 * h = h + h). intro.
  assert (h * 1 + h = h + h). auto with arith.
  rewrite <- H.
  rewrite mult_n_Sm.
  rewrite Nat.mul_comm.
  rewrite Nat.mul_comm.
  reflexivity.

  induction t; cbn; auto.
  - rewrite Nat.add_0_r.
    rewrite Nat.add_1_r.
    apply le_n_S.
    rewrite <- H.
    apply Nat.max_lub_iff.
    split; assumption.
  - apply le_n_S.
    assert (2 * h + 1 = h + S (h + 0)).
      rewrite Nat.add_0_r.
      rewrite <- Nat.add_1_r with (n := h).
      rewrite Nat.add_assoc.
      rewrite H. reflexivity.
    rewrite <- H0.
    case c, c'; apply Nat.max_lub_iff; split; auto with arith.
Qed.

Goal forall A c n (t : rbtree A c n), depth max t <= 2 * n + 1.
Proof.
  intros.
  cut (match c with
    | red => depth max t <= 2 * n + 1
    | black => depth max t <= 2 * n
  end).
  - induction c; auto with arith.
  - apply depth_max'.
Qed.

(* 4**. Chcielibyśmy teraz napisać funkcję, która wstawia element do
drzewa. Taka operacja może zepsuć własność drzewa czerwono-czarnego,
dlatego potrzebujemy zdefiniować nowy typ danych, który reprezentuje
takie pośrednie drzewo, które następnie będziemy rebalansować. Spróbuj
napisać funkcję balansowania, a następnie wstawiania elementu do
drzewa, stosując rozwiązanie Okasakiego opisane tutaj:
https://pdfs.semanticscholar.org/7756/16cf29e9c4e6d06e5999116f777e431cafa3.pdfs *)


(* -------------------------------------------------------------------------- *)


(*** Zadanie 3 - 3p *)
(* 1. Zdefiniuj indukcyjny typ danych reprezentujący termy rachunku
kombinatorów: https://pl.wikipedia.org/wiki/Rachunek_kombinatorów *)

Inductive comb := S | K | app : comb -> comb -> comb.

Notation "a · b" :=
  (app a b)
  (at level 61, left associativity).

(* 2. Zdefiniuj redukcję na termach rachunku kombinatorów.  Podstawowy
krok redukcji zdefiniowany jest przez reguły 
K t s -> t 
S r s t -> (r t) (s t)
które można stosować w dowolnym podtermie danego termu. *)

Inductive redu : comb -> comb -> Prop :=
| red_K : forall t s, redu (K · t · s) t
| red_S : forall r s t, redu (S · r · s · t) (r · t · (s · t)).

Notation "a ->p b" :=
  (redu a b)
  (at level 50, no associativity).

(* Następnie zdefiniuj relację normalizacji jako zwrotno-przechodnie domknięcie
relacji redukcji. *)

(* refl_trans_closure *)
Inductive rt_clo {A : Set} (f : A -> A -> Prop) : A -> A -> Prop :=
| rt_clo_r : forall x, rt_clo f x x
| rt_clo_t : forall a b c, f a b -> rt_clo f b c -> rt_clo f a c.

Definition redu_t : comb -> comb -> Prop := rt_clo redu.

Notation "a ->* b" :=
  (redu_t a b)
  (at level 50, no associativity).

(* 3. Zdefiniuj typ danych reprezentujący typy proste z jednym typem bazowym. *)

(* t ::= a | t -> t *)
Inductive type := alpha | appT : type -> type -> type.

Notation "a ~> b" :=
  (appT a b)
  (at level 62, right associativity).

(* 4. Zdefiniuj indukcyjny predykat, który przypisuje typy termom
rachunku kombinatorów wg poniższych reguł:
K : A -> B -> A 
S : (A -> B -> C) -> (A -> B) -> (A -> C)
M N : B jeśli M : A -> B i N : A
*)
Inductive comb_type : comb -> type -> Prop :=
| type_K : forall A B, comb_type K (A ~> B ~> A)
| type_S : forall A B C, comb_type S ((A ~> B ~> C) ~> (A ~> B) ~> (A ~> C))
| type_app : forall M N A B, 
    comb_type M (A ~> B) -> comb_type N A -> comb_type (M · N) B.

Notation "a : b" :=
  (comb_type a b)
  (at level 70, no associativity).

(* 5. Udowodnij, że redukcja zachowuje typy (subject reduction). *)

Lemma primitive_preservation : forall M N A, 
  M : A -> 
  M ->p N -> 
  N : A.
Proof.
  intros.
  induction H0.
  - inversion H. clear H. subst.
    inversion H2. clear H2. subst.
    inversion H1. clear H1. subst.
    assumption.
  - inversion H. clear H. subst.
    inversion H2. clear H2. subst. 
    inversion H1. clear H1. subst.  
    inversion H2. clear H2. subst.
    apply type_app with (M := r · t) (N := s · t) (A := B).
    + apply type_app with (A := A0); assumption.
    + apply type_app with (A := A0); assumption.
Qed.

Lemma preservation : forall M N A,
  M : A ->
  M ->* N ->
  N : A.
Proof.
  intros.
  induction H0.
  - assumption.
  - clear H1.
    apply IHrt_clo.
    apply primitive_preservation with (M := a); assumption.
Qed.

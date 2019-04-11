(*** Zadanie 0 ***)
(* Można oddawać zadania 2 i 3 z listy 5, za połowę punktów. *)

(*** Zadanie 1 - 4p ***)
(* Napisz taktykę o nazwie map, która dla zadanej funkcji oczekującej
jednego argumentu zwraca listę złożoną z wyników wywołania tej funkcji
na wszystkich przesłankach znajdujących się w kontekście, na których taka
aplikacja jest poprawnie typowana. Dopilnuj, żeby taktyka się nie zapętlała.
Np. dla kontekstu zawierającego x : nat, y : nat, z : bool
wywołanie taktyki map constr:(fun n => n+1) powinno zwrócić listę [x+1;y+1]
(kolejność elementów na liście nie jest istotna).

Do sprawdzenia typu wyrażenia służy w Ltacu konstrukcja "type of", np. 
wykonanie taktyki:

let plus1 := constr:(fun x => x+1) in
let tp := type of plus1 in
idtac tp

spowoduje wydrukowanie typu (nat -> nat).*)
Section Z1.
Require Import List.
Import ListNotations.

Ltac arg_tp f :=
  match type of f with
  | ?a -> ?b => constr:(a)
  | _ => fail
  end.

Ltac not_in h l :=
  match l with
  | nil => idtac
  | h :: _ => fail 1 "assert not_in failed"
  | _ :: ?xs => not_in h xs
  end
.
Goal forall x y : nat, True.
Proof.
  intros.
  not_in x [1].
  not_in x [y].
  (* not_in x [x]. *)
  auto.
  Qed.

Ltac map' f v :=
  let tp := arg_tp f in
  match goal with
  | [ H : _ |- _ ] => 
    let not_in := not_in H v in
    let v' := constr:(cons H v) in
    let x := eval cbv beta in (f H) in
    (* let x := eval cbv in (f H) in *)
    let res := map' f v' in
    let res' := constr:(x :: res) in
    constr:(res')
  | _ =>  constr:(@nil tp)
  end
.

Ltac map f :=
  let tp := arg_tp f in
  map' f (@nil tp)
.

Goal forall (x y : nat) (z : bool), True.
Proof.
  intros.
  let a0 := map (fun x : nat => x + 1) in
    idtac a0.
  Abort.
End Z1.

Section Z2.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import Peano.

(*** Zadanie 2 - 8p ***)
Parameter var : Set.
Hypothesis var_eq_dec : forall x y : var, {x = y} + {x <> y}.

(* Sformalizuj semantykę naturalną prostego języka imperatywnego.
Dowody twierdzeń powinny być możliwie zautomatyzowane. 

Składnia języka zawiera wyrażenia arytmetyczne, logiczne oraz instrukcje.
Zadeklaruj abstrakcyjny typ zmiennych programu var : Set.
Stan reprezentuj jako funkcję var -> Z (Z - typ liczb całkowitych).
Składnia instrukcji zawiera instrukcję pustą skip, instrukcję przypisania, 
sekwencję instrukcji, instrukcję warunkową oraz pętlę while. *)

Inductive Aop := Add | Sub | Mul
.
Inductive Aexp :=
| Anat : Z -> Aexp
| Avar : var -> Aexp
| Abin : Aexp -> Aop -> Aexp -> Aexp
. 
Inductive Bop := And | Or
.
Inductive Relop := Eq | Le 
.
Inductive Bexp := 
| Blit : bool -> Bexp
| Brel : Aexp -> Relop -> Aexp -> Bexp
| Bnot : Bexp -> Bexp
| Bbin : Bexp -> Bop -> Bexp -> Bexp
.
Inductive Com := 
| skip   : Com
| assign : var -> Aexp -> Com
| seq    : Com -> Com -> Com
| Cif    : Bexp -> Com -> Com -> Com
| while  : Bexp -> Com -> Com
.
Hint Constructors Aop.
Hint Constructors Aexp.
Hint Constructors Bop.
Hint Constructors Relop.
Hint Constructors Bexp.
Hint Constructors Com.

(* 1. Zdefiniuj funkcje ewaluacji wyrażeń arytmetycznych aeval i logicznych beval. *)
Fixpoint aeval (a : Aexp) (q : var -> Z) : Z :=
  match a with
  | Anat z => z
  | Avar x => q x
  | Abin a1 op a2 => 
    let z1 := aeval a1 q in
    let z2 := aeval a2 q in 
    match op with
    | Add => z1 + z2
    | Sub => z1 - z2
    | Mul => z1 * z2
    end
  end
.
Fixpoint beval (b : Bexp) (q : var -> Z) : bool :=
  match b with
  | Blit t => t
  | Brel a1 Eq a2 => Z.eqb (aeval a1 q) (aeval a2 q)
  | Brel a1 Le a2 => Z.leb (aeval a1 q) (aeval a2 q)
  | Bnot b1 => negb (beval b1 q)
  | Bbin b1 And b2 => andb (beval b1 q) (beval b2 q)
  | Bbin b1 Or b2 => orb (beval b1 q) (beval b2 q)
  end
.
Definition update (q : var -> Z) x z := fun y => 
  match var_eq_dec x y with
  | left _  => z 
  | right _ => q y
  end
.
(* 2. Zdefiniuj relację ceval implementującą standardową semantykę naturalną instrukcji. *)
Inductive ceval : Com -> (var -> Z) -> (var -> Z) -> Prop :=
| cskip : forall q, ceval skip q q
| cassign : forall x a q, ceval (assign x a) q (update q x (aeval a q))
| cseq : forall c1 c2 q q' q'', 
         ceval c1 q   q'' ->
         ceval c2 q'' q'  ->
         ceval (seq c1 c2) q q'
| cif_t : forall b q q' c1 c2, 
          beval b q = true ->
          ceval c1 q q' ->
          ceval (Cif b c1 c2) q q'
| cif_f : forall b q q' c1 c2, 
          beval b q = false ->
          ceval c2 q q' ->
          ceval (Cif b c1 c2) q q'
| cwhile_f : forall b c q, 
             beval b q = false ->
             ceval (while b c) q q
| cwhile_t : forall b c q q' q'', 
             beval b q = true ->
             ceval c q q'' ->
             ceval (while b c) q'' q' ->
             ceval (while b c) q q'
.
Hint Constructors ceval.

(* 3. Zdefiniuj predykat no_loop spełniony przez te i tylko te instrukcje, 
   które nie zawierają konstrukcji while. *)
Inductive no_loop : Com -> Prop :=
| no_loop_skip : no_loop skip
| no_loop_assign : forall x a, no_loop (assign x a)
| no_loop_seq : forall c1 c2, no_loop c1 -> no_loop c2 -> no_loop (seq c1 c2)
| no_loop_if : forall b c1 c2, no_loop c1 -> no_loop c2 -> no_loop (Cif b c1 c2)
.

Ltac induction_rem h b Hb :=
  remember h as b eqn:Hb; apply eq_sym in Hb; induction b;
  match goal with
  | [ H : _ |- _ ] => inversion H; trivial
  | _ => idtac
  end.

(* Udowodnij, że każda instrukcja spełniająca ten predykat zatrzymuje się. *)
Lemma no_loop_terminate : forall c, no_loop c -> forall q, exists q', ceval c q q'.
Proof.
  intros c H. induction H; intros.
  - exists q. auto.
  - exists (update q x (aeval a q)). auto.
  - destruct IHno_loop1 with (q := q). rename x into q''.
    destruct IHno_loop2 with (q := q''). rename x into q'.
    exists q'. apply cseq with (q'' := q''); auto.
  - induction_rem (beval b q) t Ht.
    + destruct IHno_loop1 with (q := q). exists x. auto.
    + destruct IHno_loop2 with (q := q). exists x. auto.
  Qed.
Require Import Coq.Program.Equality.

(* 4. Udowodnij, że pętla while true do skip nie zatrzymuje się. *)
Goal forall q, ~ exists q', ceval (while (Blit true) skip) q q'.
Proof.
  intros. intro. destruct H. dependent induction H. auto.
  Qed.

(* 5. Udowodnij twierdzenie o niezmienniku pętli: *)
Definition state := var -> Z.
Parameter P : state -> Prop.

Theorem while_invariant :
  forall (b:Bexp) (c:Com) (s s':state),
  (forall s s':state, P s -> beval b s = true -> ceval c s s' -> P s') ->
  P s -> ceval (while b c) s s' -> P s' /\ beval b s' = false.
Proof.
  intros.
  dependent induction H1; auto.
  assert (P q''). apply H with (s := s); auto.
  apply IHceval2 with (s := q'') (c0 := c); auto.
  Qed.

(* 6. 
 * Nie możemy w Coqu zapisać relacji ceval jako funkcji,
 * ale możemy napisać taką funkcję ewaluacji instrukcji, 
 * która wykonuje tylko określoną, skończoną liczbę kroków zadaną jako argument.
 * Napisz taką funkcję
 * ceval_steps : Com -> state -> nat -> option state
 * Funkcja powinna zwracać None w przypadku wyczerpania liczby kroków i 
 * (Some s) w przypadku normalnego zakończenia wykonania ze stanem s.
 *)
Fixpoint ceval_steps C s N : option state :=
  match N with
  | 0 => None (* Some s *)
  | S n => match C with
           | skip => Some s
           | assign x a => Some (update s x (aeval a s))
           | seq c1 c2 => match ceval_steps c1 s n with
                         | None => None
                         | Some s' => ceval_steps c2 s' n
                         end
           | Cif b c1 c2 => match beval b s with
                           | true  => ceval_steps c1 s n
                           | false => ceval_steps c2 s n
                           end
           | while b c => match beval b s with
                         | false => Some s
                         | true  => match ceval_steps c s n with
                                   | None => None
                                   | Some s' => ceval_steps C s' n
                                   end
                         end
           end
  end
.
(* Fixpoint ceval_steps C s N : option state * nat :=
  match N with
  | 0 => (None, 0) (* Some s *)
  | S n => match C with
           | skip => (Some s, n)
           | assign x a => (Some (update s x (aeval a s)), n)
           | seq c1 c2 => match ceval_steps c1 s n with
                         | (None, _) => (None, 0)
                         | (Some s', n') => ceval_steps c2 s' n'
                         end
           | Cif b c1 c2 => match beval b s with
                           | true  => ceval_steps c1 s n
                           | false => ceval_steps c2 s n
                           end
           | while b c => match beval b s with
                         | false => (Some s, n)
                         | true  => match ceval_steps c s n with
                                   | (None, _) => (None, 0)
                                   | (Some s', n') => ceval_steps C s' n'
                                   end
                         end
           end
  end
. *)

Lemma seq_steps : forall c1 c2 s k x,
  ceval_steps (seq c1 c2) s k = Some x ->
  exists k' s',
  S k' = k /\ ceval_steps c1 s k' = Some s' /\ ceval_steps c2 s' k' = Some x.
Proof.
  intros c1 c2 s k x H.
  induction k. inversion H.
  cbn in *.
  induction_rem (ceval_steps c1 s k) o Ho.
  exists k. exists a. auto.
  Qed.

Ltac destruct_conj_exists := 
  match goal with
  | [ H : _ /\ _ |- _ ] => destruct H; destruct_conj_exists
  | [ H : exists _, _ |- _ ] => destruct H; destruct_conj_exists
  | _ => idtac
  end
.
Ltac apply_seq_steps h := 
  apply seq_steps in h; destruct_conj_exists; subst; auto.

Lemma succ_steps : forall c i s x,
  ceval_steps c s i     = Some x ->
  ceval_steps c s (S i) = Some x
.
Proof.
  induction c; intros.
  - induction i; auto; inversion H.
  - induction i; auto; inversion H.
  - cbn. apply_seq_steps H. apply IHc1 in H0. rewrite H0. auto.
  - cbn. 
    induction_rem (beval b s) b0 Hb0;
    dependent induction i; auto; cbn in H; rewrite Hb0 in H;
    (apply IHc1 || apply IHc2); auto.
  - dependent induction i. cbn in H. inversion H.
    cbn in H.
    remember (beval b s) eqn:Hb0. dependent induction b0.
    * remember (ceval_steps c s i) eqn:Ho. induction o.
      (* induction_rem (ceval_steps c s i) o Ho. *)
      + apply IHi in H.
        apply eq_sym in Ho. apply IHc in Ho. 
        cut (
          (if beval b s
          then
            match ceval_steps c s (S i) with
            | Some s' => ceval_steps (while b c) s' (S i)
            | None => None
            end
          else Some s) = Some x); auto.
          rewrite <- Hb0 in *. rewrite Ho in *. auto.
      + inversion H.
    * cbn. rewrite <- Hb0. auto.
  Qed.
Hint Resolve succ_steps.
Lemma more_steps : forall i j,
  i <= j -> 
  forall c s x,
  ceval_steps c s i = Some x ->
  ceval_steps c s j = Some x
.
Proof.
  intros i j H.
  induction H; intros; auto.
  Qed.
Hint Resolve more_steps.

Lemma ceval_to_steps : forall c s s', ceval c s s' -> exists i, ceval_steps c s i = Some s'.
Proof.
  intros c s s' H.
  dependent induction H.
  - exists 1. auto.
  - exists 1. auto.
  - destruct IHceval1. destruct IHceval2.
    exists (1 + x + x0). cbn.
    apply more_steps with (j := x + x0) in H1; auto with arith. rewrite H1.
    apply more_steps with (i := x0); auto with arith.
  - destruct IHceval.
    exists (S x). cbn. rewrite H; auto.
  - destruct IHceval.
    exists (S x). cbn. rewrite H; auto.
  - exists 1. cbn. rewrite H. auto.
  - destruct IHceval1. destruct IHceval2.
    exists (1 + x + x0). cbn. rewrite H.
    apply more_steps with (j := x + x0) in H2; auto with arith. rewrite H2.
    apply more_steps with (i := x0); auto with arith.
  Qed.
Hint Resolve ceval_to_steps.

Lemma some_match : forall {A : Set} (y a : option A) (a' : A),
  match y with
  | Some _ => a
  | None => None
  end = Some a' -> a = Some a'.
Proof.
  intros. dependent induction y. auto. inversion H.
  Qed.

(* 7. Udowodnij własność: *)
Lemma steps_to_ceval : forall c s s', (exists i, ceval_steps c s i = Some s') -> ceval c s s'.
Proof.
  induction c; intros s s' H;
  destruct H;
  generalize dependent s;
  induction x; intros; try (intros; inversion H; trivial).
  - induction_rem (ceval_steps c1 s x) o Heqo.
    assert (exists i, ceval_steps c1 s i = Some a). exists x. auto.
    assert (exists i, ceval_steps c2 a i = Some s'). exists x. auto.
    apply IHc1 in H0. apply IHc2 in H3. apply cseq with (q'' := a); auto.
  - cbn in *. clear H1.
    induction_rem (beval b s) b0 Hb0.
    + apply cif_t; auto.
      assert (exists x, ceval_steps c1 s x = Some s'). exists x. auto. apply IHc1 in H0.
      auto.
    + apply cif_f; auto.
      assert (exists x, ceval_steps c2 s x = Some s'). exists x. auto. apply IHc2 in H0.
      auto.
  - induction_rem (beval b s) b0 Heqb0.
    + induction_rem (ceval_steps c s x) o Ho.
      apply cwhile_t with (q'' := a); auto.
      assert (exists x, ceval_steps c s x = Some a). exists x. auto.
      apply IHc in H0. auto.
    + inversion H1. subst. apply cwhile_f. auto.
  Qed.
Hint Resolve steps_to_ceval.

Goal forall c s s', ceval c s s' <-> exists i, ceval_steps c s i = Some s'.
Proof. intros. split; auto. Qed.

End Z2.

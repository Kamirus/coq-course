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
  | h :: _ => fail 1
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
  (* | [ H : _ |- _ ] => idtac acc; not_in H v; map' f (cons H v) (cons (f H) acc) *)
  (* | _ => constr:(acc) *)
  | [ H : _ |- _ ] => 
    (* idtac v; *)
    not_in H v; 
    (* idtac H; *)
    let v' := constr:(cons H v) in
    let x := constr:(f H) in
    (* let res := map' f v' in *)
    (* idtac res; *)
    (* idtac H; *)
    let xd := constr:(x :: nil) in xd
  (* | _ =>  constr:(@nil tp) *)
  end
.

Goal forall (x y : nat) (z : bool), True.
Proof.
  intros.
  (* map constr:(fun x => x+1) constr:nil constr:nil *)
  (* let a0 := map' (fun x => x+1) (@nil nat) (@nil nat) in *)
  let a0 := map' (fun x : nat => x) (@nil nat) in
    idtac a0.
  Abort.1
  auto.
Qed.
End Z1.

Section Z2.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import Peano.

(*** Zadanie 2 - 8p ***)
(* Parameter var : Set. *)
Inductive var := vr : nat -> var.

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
| Cskip   : Com
| Cassign : var -> Aexp -> Com
| Cseq    : Com -> Com -> Com
| Cif     : Bexp -> Com -> Com -> Com
| Cwhile  : Bexp -> Com -> Com
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
Lemma var_eq_dec : forall x y : var, {x = y} + {x <> y}.
Admitted.
Definition update (q : var -> Z) x z := fun y => 
  match var_eq_dec x y with
  | left _  => z 
  | right _ => q y
  end
.
(* 2. Zdefiniuj relację ceval implementującą standardową semantykę naturalną instrukcji. *)
Inductive ceval : Com -> (var -> Z) -> (var -> Z) -> Prop :=
| cskip : forall q, ceval Cskip q q
| cassign : forall x a q, ceval (Cassign x a) q (update q x (aeval a q))
| cseq : forall c1 c2 q q' q'', 
         ceval c1 q   q'' ->
         ceval c1 q'' q'  ->
         ceval (Cseq c1 c2) q q'
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
             ceval (Cwhile b c) q q
| cwhile_t : forall b c q q' q'', 
             beval b q = true ->
             ceval c q q'' ->
             ceval (Cwhile b c) q'' q' ->
             ceval (Cwhile b c) q q'
.
Hint Constructors ceval.
(* 3. Zdefiniuj predykat no_loop spełniony przez te i tylko te instrukcje, 
   które nie zawierają konstrukcji while. *)

(* Udowodnij, że każda instrukcja spełniająca ten predykat zatrzymuje się. *)

(* 4. Udowodnij, że pętla while true do skip nie zatrzymuje się. *)

(* 5. Udowodnij twierdzenie o niezmienniku pętli: *)
Parameter P : state -> Prop.

(* Theorem while_invariant :
forall (b:bexp) (c:command) (s s’:state),
(forall s s’:state, P s -> beval b s = true -> ceval s c s’ -> P s’) ->
P s -> ceval s (while b c) s’ -> P s’ /\ beval b s’ = false. *)

(* 6. 
 * Nie możemy w Coqu zapisać relacji ceval jako funkcji,
 * ale możemy napisać taką funkcję ewaluacji instrukcji, 
 * która wykonuje tylko określoną, skończoną liczbę kroków zadaną jako argument.
 * Napisz taką funkcję
 * ceval_steps : command -> state -> nat -> option state
 * Funkcja powinna zwracać None w przypadku wyczerpania liczby kroków i 
 * (Some s) w przypadku normalnego zakończenia wykonania ze stanem s.
 *)

(* 7. Udowodnij własność: *)
(* forall c s s', ceval c s s' <-> (exists i, ceval_steps c s i = Some s'). *)

End Z2.

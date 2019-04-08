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


(* Ltac guardEq a b := 
match (a = b) with
| False => fail
| True => idtac
end.
  if (a == b) then idtac else fail
.*)

Ltac guard_neq_nat a b :=
match a with
| 0 => match b with 
       | 0 => fail
       | S _ => idtac
       end
| S ?x => match b with
         | 0 => idtac
         | S ?y => guard_neq_nat x y
         end
end
.
Ltac not_in l a :=
match l with
| nil => idtac
| cons ?x ?xs => guard_neq_nat a x; not_in xs a
end
.
Goal forall n : nat, True.
Proof.
  intros.
  not_in (@nil nat) 1.
  not_in [2] 1.
  not_in [2;3] 1.
  (* not_in [n] 1. *)

Ltac map f v acc :=
  let tp := arg_tp f in
  match goal with
  | [ H : _ |- _ ] => let Htp := type of H in idtac H;
                     (not_in v H; map f (cons H v) (cons (f H) acc)) || acc
  | _ => acc
  end
.

Goal forall (x y : nat) (z : bool), True.
Proof.
  intros.
  let tp := arg_tp (fun x => x+1) in idtac tp.
  (* map constr:(fun x => x+1) constr:nil constr:nil *)
  let a0 := map (fun x => x+1) (@nil nat) (@nil nat) in
    idtac a0.
  Abort.
  auto.
Qed.
End Z1.

Section Z2.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import Peano.

(*** Zadanie 2 - 8p ***)
Parameter var : Set.

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


(* 2. Zdefiniuj relację ceval implementującą standardową semantykę naturalną instrukcji. *)

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

(*** Zadanie 0 ***)
(* Można oddawać zadania 2 i 3 z listy 5, za połowę punktów. *)

Section Z1.
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
End Z1.

Section Z2.
(*** Zadanie 2 - 8p ***)
(* Sformalizuj semantykę naturalną prostego języka imperatywnego.
Dowody twierdzeń powinny być możliwie zautomatyzowane. 

Składnia języka zawiera wyrażenia arytmetyczne, logiczne oraz instrukcje. 
Zadeklaruj abstrakcyjny typ zmiennych programu var : Set.
Stan reprezentuj jako funkcję var -> Z (Z - typ liczb całkowitych).
Składnia instrukcji zawiera instrukcję pustą skip, instrukcję przypisania, 
sekwencję instrukcji, instrukcję warunkową oraz pętlę while. *)

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

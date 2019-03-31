(*** Zadanie 1 - 3p *)
(*Rozważmy typ list indeksowanych długością

Inductive llist {A:Set} : nat -> Set := 
| lnil : llist 0 
| lcons : forall n, A -> llist n -> llist (S n).

1. Zdefiniuj funkcję konwersji zwykłych list do typu llist oraz vice
versa: inject : forall (A : Type) (ls : list A), ilist (length ls)
unject : forall (A : Type) (n : nat), ilist n -> list A

2. Udowodnij, że złożenie unject o inject jest identycznością.
3. Udowodnij, że złożenie inject o unject jest
identycznością. Tej własności nie da się zapisać wprost w Coqu - w tym przypadku powstaje problem z typowaniem równości
inject (unject ls) = ls

Rozwiąż ten problem na dwa sposoby:
a. Zdefiniuj własny typ równości na listach llist_eq, udowodnij, że jest to relacja równoważności i udowodnij, że dla wszystkich list zachodzi
llist_eq (inject (unject ls)) ls
b. Zdefiniuj funkcję, która wykonuje koercję elementów typu llist n do typu llist (length (unject ls)) i wykorzystaj ją do sformułowania lematu.
 *)

(*** Zadanie 2 - 6p *)
(*

1. Zdefiniuj predykat sorted : list nat -> Prop spełniony dla list
posortowanych rosnąco.

2. Napisz funkcję sortowania przez wstawianie o następującej
specyfikacji:

Require Import Permutation.

Definition insertion_sort : forall l : list nat, {l' : list nat |
Permutation l l' /\ sorted l'}.  *)

(*** Zadanie 3 - 8p *)
(*
Rozwiąż poprzednie zadanie używając typu danych sorted_list indeksowanych typem option nat takich, że sorted_list None reprezentuje listę pustą, a sorted_list (Some n) jest typem list posortowanych rosnąco, których najmniejszym elementem jest n.

1. Zdefiniuj tak określony indukcyjny typ danych sorted_list.
2. Napisz funkcję insert, która wstawia element do sorted_list.
3. Dowolną listę posortowaną rosnąco określa para złożona z indeksu x i listy typu sorted_list x. Napisz specyfikację funkcji insertion_sort przy użyciu tego typu oraz zdefiniuj tę funkcję.
(*** Zadanie 1 - 1p ***)
(* Rozważmy alternatywną definicję predykatu <=

Definition le2 n m := exists k, m = n + k.

1. Udowodnij równoważność le2 i Coqowej definicji le.  2. Zapisz
definicję le2 w sposób równoważny jako predykat definiowany
indukcyjnie. Dowód z punktu 1 powinien być nadal poprawny przy nowej
definicji le2.

 *)

(*** Zadanie 2 - 4p ***)
(* Rozważmy zasadę indukcji noetherowskiej na zbiorze liczb
naturalnych z porządkiem <=

forall P : nat -> Prop, 
(forall n, (forall m, m < n -> P m) -> P n) ->
forall n, P n.

Udowodnij tę zasadę korzystając z indukcji matematycznej (tzn. z
twierdzenia nat_ind). [Uwaga: trzeba wzmocnić hipotezę indukcyjną.]
*)

(*** Zadanie 3 - 3p [+ 5p*] ***)
(* 1. Zdefiniuj funkcję fib : nat -> nat wyznaczającą kolejne liczby
Fibonacciego wprost z definicji:

F_0 = 0 
F_1 = 1 
F_n = F_(n-1) + F_(n-2)

2. Udowodnij cel

Goal forall n, n > 0 -> fib n > 0.

Jakiej zasady indukcji potrzebujesz?

3*. Udowodnij następującą własność liczb Fibonacciego: Jeśli n jest
podzielne przez 3, to fib n jest liczbą parzystą, a jeśli n nie jest
podzielne przez 3, to fib n jest liczbą nieparzystą. [Zdefiniuj
predykaty parzystości i nieparzystości wzajemnie indukcyjnie.]

4*. Zdefiniuj i udowodnij zasadę indukcji odzwierciedlającą schemat
wywołań rekurencyjnych funkcji Fibonacciego. Użyj jej do udowodnienia
twierdzenia z punktu 2.

 *)

(*** Zadanie 4 - 3p ***)
(*

1. Zdefiniuj indukcyjny predykat sub taki, że sub l1 l2 zachodzi wtw gdy l1 jest podlistą l2
(tj. l1 zawiera pewien podciąg elementów l2).

2. Udowodnij, że wynik działania funkcji filter jest podlistą
argumentu tej funkcji: *)

Require Import List.

Inductive sub (A : Type) : list A -> list A -> Prop := ...

Lemma filter_sublist:
forall (A : Type) (f : A -> bool) l1 l2, l2 = filter f l1 -> sub l2 l1.

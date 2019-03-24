(*** Zadanie 1 - 4p *)

(* Struktury algebraiczne możemy wygodnie reprezentować w Coqu za
pomocą rekordów zależnych, których pola opisują własności definiujące
daną strukturę. *)

(* 1. Zapoznaj się z komendą Record. *)

(* 2. Zdefiniuj typ monoidu jako rekord zależny, zawierający odpowiednie
pola, w tym łączność operacji i obustronną neutralność wyróżnionego
elementu. *)

(* 3. Udowodnij, że w każdym monoidzie istnieje dokładnie jeden element
neutralny. *)

(* 4. Zdefiniuj w Coqu pojęcie homomorfizmu między monoidami. *)

(* 5. Podaj dwa przykłady monoidów i zainstaluj je w typie monoid. Napisz
funkcję pomiędzy nośnikami tych monoidów, która definiuje homomorfizm
pomiędzy nimi. Udowodnij, że jest to homomorfizm. *)

(* 6. Record jest cukrem syntaktycznym. W jaki sposób za pomocą znanych
konstrukcji Coqa możemy inaczej zdefiniować typ monoid? *)


(* -------------------------------------------------------------------------- *)


(*** Zadanie 2 - 4p + 10p *)

(* 1. Zdefiniuj indukcyjny typ danych reprezentujący drzewa
czerwono-czarne  *)
(* rbtree : Set -> color -> nat -> Set *)

(* taki, że typ rbtree A c h reprezentuje drzewa zawierające elementy
typu A, których korzeń ma kolor c i głębokość czarnych węzłów h. *)

(* 2. Zdefiniuj funkcję  *)
(* depth : forall {A : Set} {c : color} {n : nat},
(nat -> nat -> nat) -> rbtree A c n -> nat *)

(* pozwalającą obliczyć maksymalną i minimalną głębokość drzewa, w
zależności od tego, jaką funkcję podamy jako argument. *)

(* 3. Udowodnij własności  *)
(* forall A c n (t : rbtree A c n), depth min t >= n  *)
(* forall A c n (t : rbtree A c n), depth max t <= 2*n + 1. *)

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

(* 2. Zdefiniuj redukcję na termach rachunku kombinatorów.  Podstawowy
krok redukcji zdefiniowany jest przez reguły 
K t s -> t 
S r s t -> (r t) (s t)
które można stosować w dowolnym podtermie danego termu. *)

(* Następnie zdefiniuj relację normalizacji jako zwrotno-przechodnie domknięcie
relacji redukcji. *)

(* 3. Zdefiniuj typ danych reprezentujący typy proste z jednym typem bazowym. *)

(* 4. Zdefiniuj indukcyjny predykat, który przypisuje typy termom
rachunku kombinatorów wg poniższych reguł:
K : A -> B -> A 
S : (A -> B -> C) -> (A -> B) -> (A -> C)
M N : B jeśli M : A -> B i N : A
*)

(* 5. Udowodnij, że redukcja zachowuje typy (subject reduction). *)


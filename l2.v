(*** Zadanie 1 - 1p ***)
(* 
1. Zdefiniuj typ pusty z co najmniej jednym konstruktorem i udowodnij cel 
*)
Inductive empty : Set := .

Goal forall x:empty, true = false.
Proof.
  intro.
  destruct x.
Qed.

(* 
2. Zdefiniuj typ zamieszkany przez dokładnie jeden element i udowodnij cel 
*)

Inductive unit : Set := 
  | I : unit.

Goal forall x y : unit, x = y.
Proof.
  intros.
  destruct x; destruct y.
  reflexivity.
Qed.

(*** Zadanie 2 - 3p ***)
(* Rozważmy typ danych do reprezentacji formuł logiki pierwszego rzędu
interpretowanych w zbiorze liczb naturalnych: *)

Inductive form : Set :=
| Eq : nat -> nat -> form (* formuła atomowa opisująca rowność liczb *)
| Neg : form -> form (* negacja *)
| Conj : form -> form -> form (* koniunkcja *)
| Forall : (nat -> form) -> form. (* kwantyfikator ogólny *)

(* Zauważ, że w tej reprezentacji nie potrzebujemy używać zmiennych,
ponieważ kwantyfikator wiążący zmienne jest reprezentowany przez
funkcję Coqa. *)

(* 1. Zdefiniuj funkcję *)
(* interpret : form -> Prop, *)
Fixpoint interpret (x : form) : Prop := 
  match x with
  | Eq a b => a = b
  | Neg x => ~ (interpret x)
  | Conj a b => interpret a /\ interpret b
  | Forall f => forall n, interpret (f n)
  end.

(* a -> b *)
(* ~a \/ b *)
(* ~(a /\ ~b) *)
Notation "a ~> b" := 
  (Neg (Conj a (Neg b)))
  (at level 60, right associativity).

(* która tłumaczy takie reprezentacje formuł na odpowiadające im formuły
Coqa.

2. Napisz kilka przykładów reprezentacji formuł (ozn. A). Dla których
z nich potrafisz udowodnic cel 
Goal interpret A.  ? *)
Definition phi1 := Forall (fun n => Eq n n).
Goal interpret phi1.
Proof.
  simpl.
  intro.
  reflexivity.
Qed.

Definition phi2 := 
  Forall (fun n => 
    Forall (fun m => Eq n m ~> Eq m n )).
Goal interpret phi2.
Proof.
  simpl.
  intros n m.
  intro.
  apply H.
  symmetry.
  apply H.
Qed.

Definition phi3 := 
  Forall (fun a => 
    Forall (fun b => 
      Forall (fun c => (Conj (Eq a b) (Eq b c)) ~> Eq a c ))).
Goal interpret phi3.
Proof.
  simpl.
  intros a b c.
  intro.
  destruct H; destruct H0.
  destruct H.
  rewrite H; rewrite H0; reflexivity.
Qed.

(* 3. Napisz alternatywną reprezentację formuł z jawnym użyciem
zmiennych, w której wszystkie konstruktory mają argumenty typu
bazowego (nie funkcyjnego). Co jest teraz potrzebne, żeby zdefiniować
funkcję interpret?

Możesz przyjąć, że zmienne są typu string. Przykład użycia poniżej. *)

Require Import String.
Definition var := string.
Eval compute in (if string_dec "a" "b" then 1 else 2). (* porównanie napisów *)

Inductive form' : Set :=
| Eq' : string -> string -> form' (* formuła atomowa opisująca rowność liczb *)
| Neg' : form' -> form' (* negacja *)
| Conj' : form' -> form' -> form' (* koniunkcja *)
| Forall' : string -> form' -> form'. (* kwantyfikator ogólny *)

Definition ksi1 := Forall' "x" (Eq' "x" "x").

(* ????? *)

(*** Zadanie 3 - 4p ***)
(* 1. Zdefiniuj typ num do reprezentacji numerałów Churcha. *)

Definition num := forall A : Type, (A -> A) -> A -> A.

Definition zero : num := fun (A: Type) s => fun z => z.

(* 2. Zdefiniuj funkcję konwersji numerałów do liczb naturalnych
 num_to_nat : num -> nat *)
Definition num_to_nat (n : num) : nat := n nat (fun x => x + 1) 0.

(* 3. Zdefiniuj funkcje następnika, dodawania i mnożenia dla numerałów
Churcha 
succ : num -> num 
add : num -> num -> num 
mult : num -> num -> num *)

Definition succ (n : num) : num := 
  fun (X : Type) (s : X -> X) (z : X) => s (n X s z).

Definition add (n : num) (m : num) : num := 
  fun (X : Type) s z => n X s (m X s z).

Definition mult (n : num) (m : num) : num := 
  fun (X : Type) s z => n X (fun x => m X s x) z.

(* 4. Udowodnij poprawność tych definicji (zastanów się, co to znaczy). *) 

Goal forall (n : nat) (ch : num), n = num_to_nat ch -> num_to_nat (succ ch) = n + 1.
Proof.
  intros.
  rewrite H.
  unfold num_to_nat.
  unfold succ.
  reflexivity.
Qed.

Goal forall (n : num), add zero n = n.
Proof.
  intros.
  unfold add.
  unfold zero.
  
Qed.

(* Goal forall (n : nat) (n' : num) (m : nat) (m' : num),
  num_to_nat n' = n /\ num_to_nat m' = m -> 
  num_to_nat (add n' m') = n + m.
Proof.
  intros.
  destruct H as [HN HM].
  (* rewrite <- HM.
  rewrite <- HN.
  unfold add.
  unfold num_to_nat. *)
  induction m.
    - unfold num_to_nat in HM; unfold num_to_nat in HN.
      unfold num_to_nat.
      unfold add.
      rewrite HM.
      rewrite HN.
      trivial.
    - rewrite <- HN.
      rewrite <- HM.
      unfold add.
      unfold num_to_nat.
    apply IHm with (m := S m) in HM as H0.
      unfold num_to_nat.
      unfold add.
    (* rewrite HM; rewrite HN; unfold add; unfold num_to_nat. *)
  .
Qed. *)

(*** Zadanie 4 - 4p ***)
(* 1. Zdefiniuj typ btree do reprezentacji drzew binarnych
etykietowanych w węzłach liczbami naturalnymi.*)
Inductive btree := 
| Leaf : btree
| Node : btree -> nat -> btree -> btree.

Fixpoint eq_nat n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.

(* 2. Napisz funkcję has_label : btree -> nat -> bool, która sprawdza,
czy drzewo zawiera daną etykietę. *)
Fixpoint has_label (t : btree) (n : nat) : bool :=
  match t with
  | Leaf => false
  | Node t1 m t2 => eq_nat m n || has_label t1 n || has_label t2 n
  end.

Compute has_label (Node Leaf 123 Leaf) 123.
Compute has_label (Node Leaf 123 Leaf) 0.
Compute has_label (Node (Node Leaf 0 Leaf) 123 Leaf) 0.

(* 3. Zdefiniuj drugi typ bbtree do reprezentacji tych samych drzew w ten
sposób, że konstruktor węzła ma dwa argumenty: etykietę oraz funkcję
typu bool -> bbtree, która zwraca lewe poddrzewo dla argumentu true i
prawe - dla argumentu false.  Zdefiniuj funkcję has_label dla tej
reprezentacji. *)
Inductive bbtree := 
| LLeaf : bbtree
| NNode : nat -> (bool -> bbtree) -> bbtree.

Fixpoint hhas_label (t : bbtree) (n : nat) : bool :=
  match t with
  | LLeaf => false
  | NNode m f => eq_nat m n || hhas_label (f true) n || hhas_label (f false) n
  end.

Compute hhas_label (NNode 123 (fun _ => LLeaf)) 123.
Compute hhas_label (NNode 123 (fun _ => LLeaf)) 0.
Compute hhas_label (NNode 123 (fun x => if x then (NNode 0 (fun _ => LLeaf)) else LLeaf)) 0.

(* 4. Napisz funkcje konwertujące typ btree do bbtree i na odwrót. *)
Definition packb (A : Set) (x : A) (y : A) : bool -> A :=
  fun b => if b then x else y.

Fixpoint btobb (b : btree) : bbtree := 
  match b with
  | Leaf => LLeaf
  | Node b1 n b2 => 
    let b1 := btobb b1 in
    let b2 := btobb b2 in
    NNode n (packb bbtree b1 b2)
  end.

Fixpoint bbtob (b : bbtree) : btree :=
  match b with
  | LLeaf => Leaf
  | NNode n f => Node (bbtob (f true)) n (bbtob (f false))
  end.

(* 5. Udowodnij, że te funkcje definiują bijekcję miedzy tymi typami.  *)

(*** Zadanie 5 - 4p ***)
(*

1. Napisz funkcję nth : list A -> nat -> option A zwracającą n-ty
element listy o elementach pewnego typu A. W razie, gdy lista ma mniej
niż n+1 elementów, funkcja zwraca None; w przeciwnym razie funkcja
zwraca Some a, gdzie a jest n-tym elementem listy.  *)

Variable A : Set.

Definition nth : list A -> nat -> option A.

(* 2. Udowodnij wlasność nth_in (nie używając taktyk automatycznych
ani lematów bibliotecznych). *)

Lemma nth_in:forall n l, n < length l -> exists a:A, nth l n = Some a. 

(*** Zadanie 6 - 4p ***)
(* Udowodnij cel *)

Goal nat <> bool.

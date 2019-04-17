Require Import Arith.

Definition ret {A : Type} (x : A) := Some x.
 
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).

Notation "X <-- A ; B" :=
  (bind A (fun X => B))
  (right associativity, at level 60).

Require Import QArith.
Local Open Scope Q_scope.
Require Import List.
Import ListNotations.

(* a) Define an inductive type exp of expressions over rationals
(which inhabit the Coq type Q).
Include variables (represented as natural numbers), constants, addition,
subtraction, and multiplication. *)
Inductive exp :=
| var : nat -> exp
| const : Q -> exp
| add : exp -> exp -> exp
| sub : exp -> exp -> exp
| mul : exp -> exp -> exp
.

(* b) Define a function lookup for reading an element out of a list of rationals,
by its position in the list. *)
Fixpoint lookup (i : nat) (env : list Q) := List.nth i env 0.
(* Fixpoint lookup (i : nat) (env : list Q) : Nat.lt i (length env) -> Q.
  refine (
    match env, i with
    | [], _ => fun h => _
    | x :: _, O => fun _ => x
    | _ :: env', S i' => fun pf => lookup i' env' _
    end
  ).
  cbn in h. apply lt_0 in h. contradiction.
  cbn in pf. auto with arith.
Defined. *)

(* c) Define a function expDenote that translates exps,
along with lists of rationals representing variable values, to Q . *)
Fixpoint expDenote (e : exp) (env : list Q) : Q :=
  match e with
  | var x => lookup x env
  | const a => a
  | add e1 e2 => expDenote e1 env + expDenote e2 env
  | sub e1 e2 => expDenote e1 env - expDenote e2 env
  | mul e1 e2 => expDenote e1 env * expDenote e2 env
  end
.

Load DepList.

(* d) Define a recursive function eqsDenote over list ( exp × Q ),
characterizing when all of the equations are true. *)
Fixpoint eqsDenote env (es : list (exp * Q)) :=
  match es with
  | nil => True
  | (e, q) :: es' => expDenote e env == q /\ eqsDenote env es'
  end
.

(* e) Fix a representation lhs of flattened expressions.
Where len is the number of variables,
represent a flattened equation as ilist Q len.
Each position of the list gives the coeficient of the corresponding variable. *)
Definition lhs len := ilist Q len.

(* (f) Write a recursive function linearize that takes a constant k
and an expression e and optionally returns an lhs equivalent to k × e.
This function returns None when it discovers the input expression is not linear.
The parameter len of lhs should be a parameter of linearize, too.
The functions: singleton, everywhere, and map2 from DepList will probably be helpful.
It is also helpful to know that Qplus is the identifier for rational addition *)
Fixpoint toConst (e : exp) : option Q :=
  match e with
  | var _ => None
  | const a => Some a
  | add e1 e2 => match toConst e1, toConst e2 with
                | Some c1, Some c2 => Some (c1 + c2)
                | _, _ => None
                end
  | sub e1 e2 => match toConst e1, toConst e2 with
                | Some c1, Some c2 => Some (c1 - c2)
                | _, _ => None
                end
  | mul e1 e2 => match toConst e1, toConst e2 with
                | Some c1, Some c2 => Some (c1 * c2)
                | _, _ => None
                end
  end
.
Fixpoint linearize (k : Q) (e : exp) (len : nat) : option (lhs len) :=
  match e with
  | var x => Some (singleton k 0 len x)
  | const _ => None
  | add e1 e2 =>
    l1 <-- linearize k e1 len ;
    l2 <-- linearize k e2 len ;
    ret (map2 Qplus l1 l2)
  | sub e1 e2 =>
    l1 <-- linearize k e1 len ;
    l2 <-- linearize k e2 len ;
    ret (map2 Qminus l1 l2)
  | mul e1 e2 => match toConst e1, toConst e2 with
                | Some c1, None => linearize (c1 * k) e2 len
                | None, Some c2 => linearize (c2 * k) e1 len
                | _, _ => None
                end
  end
.

(* g) Write a recursive function linearizeEqs : list (exp × Q) → option (lhs × Q).
This function linearizes all of the equations in the list in turn,
building up the sum of the equations.
It returns None if the linearization of any constituent equation fails. *)
Fixpoint linearizeEqs (len : nat) (eqs : list (exp * Q)) : option (lhs len * Q) :=
  match eqs with
  | [] => Some (everywhere 0 len, 0)
  | (e, q) :: eqs' => 
      r <-- linearizeEqs len eqs' ;
      let (reslhs, resq) := r in
      lhs <-- linearize 1 e len ;
      ret (map2 Qplus reslhs lhs, q + resq)
  end
.

(* h) Define a denotation function for lhs *)
Fixpoint range k len : ilist nat len := 
  match len with
  | 0%nat => INil
  | (S n)%nat => ICons k (range (k + 1)%nat n)
  end
.
Compute range O 3.

Definition foldri {A B : Type} (f : nat -> A -> B -> B) (acc : B) len (il : ilist A len) : B :=
  let fix foldri' k n (il : ilist A n) :=
    match il with
    | INil => acc
    | ICons _ x il' => f k x (foldri' (k + 1)%nat _ il')
    end
  in
  foldri' 0%nat len il
.
Compute (@foldri nat nat (fun i a acc => (acc + i * a)%nat) 0%nat _ (singleton 1%nat O 4 3)).

Definition lhsDenote len env (l : lhs len) : Q :=
  (* let indexes := range 0%nat len in *)
  (* let li : ilist (nat * Q) len := map2 (fun a b => (a%nat ,b%Q)) indexes l in *)
  let f := fun x a acc => lookup x env * a + acc in
  foldri f 0 l
.

Require Import Coq.Program.Equality.

(* i) Prove: when exp linearization succeeds on constant k and expression e,
the linearized version has the same meaning as k × e. *)
Lemma lin_ok : forall e len lhs k,
  linearize k e len = Some lhs -> forall env, 
  lhsDenote env lhs = k * expDenote e env.
  intro.
  dependent induction e; intros.
  - cbn in *. inversion H.
    induction len. cbn.

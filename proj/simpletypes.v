
Require Import String.
Require Import List.

(* utils *)

Definition ret {A : Type} (x : A) := Some x.
 
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.
  
Definition guard (b : bool) : option unit := if b then Some tt else None.

Hint Unfold ret bind guard.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).

Notation "X <-- A ; B" :=
  (bind A (fun X => B))
  (right associativity, at level 60).

Notation "A ;; B" :=
  (bind A (fun _ => B))
  (right associativity, at level 60).

(* tactics *)

Ltac try_inv :=
  match goal with
  | [ H : _ |- _ ] => solve [inversion H; auto]
  | _ => idtac
  end.

Ltac ind_rem h b Hb :=
  remember h as b eqn:Hb;
  (* apply eq_sym in Hb; *)
  induction b;
  cbn in *;
  try_inv.

Ltac di h := destruct h; try_inv; cbn in *.

(* main *)

Definition var := string.
(*
Eval compute in (if string_dec "a" "b" then 1 else 2). (* porównanie napisów *)
Eval compute in (if string_dec "a" "a" then 1 else 2). (* porównanie napisów *)
*)

Inductive type :=
| typebool : type
| typevar : var -> type
| typelam : type -> type -> type
.
Notation "a ~> b" :=
  (typelam a b)
  (at level 62, right associativity)
.
Fixpoint type_eq (a b : type) : bool :=
  match a, b with
  | typebool, typebool => true
  | typevar x, typevar y => if string_dec x y then true else false
  | a1 ~> a2, b1 ~> b2 => andb (type_eq a1 b1) (type_eq a2 b2)
  | _, _ => false
  end
.
Inductive term :=
| termvar : var -> term
| lam : var -> type -> term -> term
| termapp : term -> term -> term
.
Notation "M · N" :=
  (termapp M N)
  (at level 61, left associativity)
.
Definition ctx := list (var * type)
.
Fixpoint lookup (G : ctx) (x : var) : option type :=
  match G with
  | nil => None
  | (v, t) :: G' => if string_dec v x then Some t else lookup G' x
  end
.
Inductive has_type : ctx -> term -> type -> Prop :=
| var_has_type : forall G x a, lookup G x = Some a -> has_type G (termvar x) a
| lam_has_type : forall G x M (a b : type),
  has_type ((x, b) :: G) M a ->
  has_type G (lam x b M) (b ~> a)
| app_has_type : forall G (M N : term) (a b : type),
  has_type G M (a ~> b) -> has_type G N a -> has_type G (M · N) b
.
Hint Constructors has_type term type.

Reserved Notation "'[' x ':=' N ']' M" (at level 20).

Fixpoint subst (x : var) (N M : term) : term :=
  match M with
  | termvar y => if string_dec x y then N else M
  | lam y a M' => if string_dec x y then M else lam y a ([x := N] M')
  | M1 · M2 => ([x := N] M1) · ([x := N] M2)
  end
where "'[' x ':=' N ']' M" := (subst x N M).

Inductive value : term -> Prop :=
| v_lam : forall x a M, value (lam x a M)
.
Hint Constructors value.


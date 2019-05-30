
Require Import String.
Require Import List.

(* utils *)

Definition ret {A : Type} (x : A) := Some x.
 
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.
  
Definition guard (b : bool) := if b then Some unit else None.

Hint Unfold ret bind guard.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).

Notation "X <-- A ; B" :=
  (bind A (fun X => B))
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

(* main *)

Definition var := string.
(*
Eval compute in (if string_dec "a" "b" then 1 else 2). (* porównanie napisów *)
Eval compute in (if string_dec "a" "a" then 1 else 2). (* porównanie napisów *)
*)

Inductive type :=
| typevar : var -> type
| typelam : type -> type -> type
.
Notation "a ~> b" :=
  (typelam a b)
  (at level 62, right associativity)
.
Fixpoint type_eq (a b : type) : bool :=
  match a, b with
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

Fixpoint infer (G : ctx) (M : term) : option type :=
  match M with
  | termvar x => lookup G x
  | lam x a N => 
    b <-- infer ((x, a) :: G) N ;
    ret (a ~> b)
  | M1 · M2 => 
    match infer G M1 with
    | Some (a ~> b) => 
      a' <-- check G M2 a ;
      ret b
    | _ => None
    end
  end
with check (G : ctx) (M : term) (A : type) : option type :=
  match M with
  | termvar x =>
    a <-- lookup G x ;
    m <-- guard (type_eq A a) ; 
    ret A
  | lam x a N => 
    match A with
    | a' ~> b =>
      m <-- guard (type_eq a' a) ;
      check ((x, a) :: G) N b
    | _ => None
    end
  | M1 · M2 => 
    match infer G M1 with
    | Some (a2 ~> a) => 
      m <-- guard (type_eq a A) ;
      check G M2 a2
    | _ => None
    end
  (* | _ => 
    a' <-- infer G M ;
    if type_eq a a' then Some a else None *)
  end
.

Definition x := termvar "x"%string.
Definition y := termvar "y"%string.
Definition z := termvar "z"%string.
Definition a := typevar "a"%string.
Definition b := typevar "b"%string.
Definition c := typevar "c"%string.
Compute infer nil (lam "x"%string a x).
Compute infer nil 
  (lam "x"%string (b ~> c) 
    (lam "y"%string (a ~> b)
      (lam "z"%string a (x · (y · z))))).

(* Lemma check_to_infer : forall G M, check G M a = Some b *)

Lemma infer_lam : forall G v t M a, infer G (lam v t M) = Some a ->
  exists b, a = t ~> b /\ infer ((v, t) :: G) M = Some b.
Proof.
  intros.
  cbn in H.
  ind_rem (infer ((v, t) :: G) M) im Him.
  inversion H; subst; clear H.
  exists a1; auto.
  Qed.

Lemma infer_app : forall G M1 M2 a, infer G (M1 · M2) = Some a ->
  exists b c, infer G M1 = Some (b ~> a) /\ check G M2 b = Some c.
Proof.
  intros.
  ind_rem (infer G (M1 · M2)) im Him.
  ind_rem (infer G M1) im1 Him1.
  destruct a2; try_inv.
  ind_rem (check G M2 a2_1) cm2 Hcm2.
  inversion H. inversion Him. subst. clear H Him.
  exists a2_1. exists a2.
  auto.
  Qed.

Lemma infer_ok : forall G M a, infer G M = Some a -> has_type G M a.
Proof.
  intros. generalize dependent a0. generalize dependent G.
  induction M; intros.
  - constructor. admit.
  - apply infer_lam in H as H1; destruct H1 as [ b H1 ];
      destruct H1 as [H0 H1]; rewrite H0 in *; clear H0.
    constructor.
    apply IHM.
    assumption.
  - apply infer_app in H as H1; 
      destruct H1 as [b H1]; destruct H1 as [c H1]; destruct H1 as [H1 H2].
  Qed.

Theorem typecheck : forall (G : ctx) (M : term), option { A : type | has_type G M A }.
Proof.
  intros.
  case (infer G M).
  - intro.
  Qed.
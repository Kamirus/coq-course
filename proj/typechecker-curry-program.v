
Require Import String.
Require Import List.

(* utils *)

Check exist.

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

Notation "'[' x ',' H ']' <-- A ; B" :=
  (match A with
  | Some (exist _ x H) => B
  | None => None
  end)
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
(* | typebool : type *)
| typevar : var -> type
| typelam : type -> type -> type
.
Notation "a ~> b" :=
  (typelam a b)
  (at level 62, right associativity)
.
Fixpoint type_eq (a b : type) : bool :=
  match a, b with
  (* | typebool, typebool => true *)
  | typevar x, typevar y => if string_dec x y then true else false
  | a1 ~> a2, b1 ~> b2 => andb (type_eq a1 b1) (type_eq a2 b2)
  | _, _ => false
  end
.
Inductive term :=
(* | termbool : bool -> term
| termif : term -> term -> term -> term *)
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
(* | bool_has_type : forall G b, has_type G (termbool b) typebool
| if_has_type : forall G b c1 c2 a,
  has_type G b typebool ->
  has_type G c1 a -> 
  has_type G c2 a -> 
  has_type G (termif b c1 c2) a *)
| var_has_type : forall G x a, lookup G x = Some a -> has_type G (termvar x) a
| lam_has_type : forall G x M (a b : type),
  has_type ((x, b) :: G) M a ->
  has_type G (lam x b M) (b ~> a)
| app_has_type : forall G (M N : term) (a b : type),
  has_type G M (a ~> b) -> has_type G N a -> has_type G (M · N) b
.
Hint Constructors has_type term type.

Inductive iterm :=
(* | itermbool : bool -> iterm *)
(* | itermif : cterm -> cterm -> cterm -> iterm *)
| itermvar : var -> iterm
| ilam : var -> type -> cterm -> iterm
| itermapp : cterm -> cterm -> iterm
with cterm :=
| C : iterm -> cterm
.

Fixpoint term_to_iterm M :=
  let I x := C (term_to_iterm x) in
  match M with
  (* | termbool b => itermbool b *)
  (* | termif b c1 c2 => itermif (I b) (I c1) (I c2) *)
  | termvar x => itermvar x
  | lam x a N => ilam x a (I N)
  | termapp M1 M2 => itermapp (I M1) (I M2)
  end
.

Definition unC cM :=
  match cM with
  | C M => M
  end.
Hint Unfold unC.

Fixpoint iterm_to_term iM :=
  let T x := iterm_to_term (unC x) in
  match iM with
  (* | itermbool b => termbool b *)
  (* | itermif (C b) (C c1) (C c2) => termif (T b) (T c1) (T c2) *)
  | itermvar x => termvar x
  | ilam x a cN => lam x a (T cN)
  | itermapp cM1 cM2 => (T cM1) · (T cM2)
  end
.

Program Fixpoint infer (G : ctx) (M : iterm) : 
    option { A : type | has_type G (iterm_to_term M) A } :=
  match M with
  (* | itermbool _ => ret (exist typebool _) *)
  (* | itermif cb (C c1) cc2 =>
    check G cb typebool ;;
    a <-- infer G c1 ;
    check G cc2 a ;;
    ret a *)
  | itermvar x => 
    a <-- lookup G x ;
    ret (exist _ a (var_has_type G x a _))
  | ilam x a (C N) => 
    [b, H] <-- infer ((x, a) :: G) N ;
    ret (exist _ (a ~> b) _)
  | itermapp (C M1) cM2 => 
    match infer G M1 with
    | Some (exist _ (a ~> b) Hm1) => 
      [a', Hm2] <-- check G cM2 a ;
      ret (exist _ b _)
    | _ => None
    end
  end
with check (G : ctx) (M : cterm) (A : type) : 
    option { A : type | has_type G (iterm_to_term (unC M)) A } :=
  match M with
  | C M =>  
    [a, H] <-- infer G M ;
    guard (type_eq A a) ;;
    ret (exist _ A _)
  end
.
Obligation 1 of infer.

Definition vx := termvar "x"%string.
Definition vy := termvar "y"%string.
Definition vz := termvar "z"%string.
Definition va := typevar "a"%string.
Definition vb := typevar "b"%string.
Definition vc := typevar "c"%string.
Compute infer nil (lam "x"%string va vx).
Compute infer nil 
  (lam "x"%string (vb ~> vc) 
    (lam "y"%string (va ~> vb)
      (lam "z"%string va (vx · (vy · vz))))).

Lemma from_guard_type_eq : forall a b, Some tt = guard (type_eq a b) -> a = b.
Proof.
  intros.
  generalize dependent b. induction a; intros.
  { ind_rem (type_eq typebool b) t Ht. di b. } 
  { ind_rem (type_eq (typevar v) b) t Ht. di b. di (string_dec v v0). }
  { ind_rem (type_eq (a1 ~> a2) b) t Ht. di b. 
    ind_rem (type_eq a1 b1) t1 Ht1.
    assert (guard (type_eq a1 b1) = Some tt). rewrite <- Ht1; auto.
    assert (guard (type_eq a2 b2) = Some tt). rewrite <- Ht; auto.
    rewrite IHa1 with b1; auto.
    rewrite IHa2 with b2; auto.
  }
  Qed.

Lemma check_lam : forall G v t M a, check G (lam v t M) a = Some tt ->
  exists b, a = t ~> b /\ check ((v, t) :: G) M b = Some tt.
Proof.
  intros.
  cbn in H.
  di a.
  ind_rem (guard (type_eq a1 t)) g Hg.
  exists a2. split; auto.
  di a; apply from_guard_type_eq in Hg. rewrite Hg. reflexivity.
  Qed.

Lemma check_app : forall G M1 M2 a, check G (M1 · M2) a = Some tt ->
  exists b, infer G M1 = Some (b ~> a) /\ check G M2 b = Some tt.
Proof.
  intros.
  ind_rem (check G (M1 · M2) a) ch Hch.
  ind_rem (infer G M1) im1 Him1.
  di a1.
  ind_rem (guard (type_eq a1_2 a)) g Hg.
  di a1; apply from_guard_type_eq in Hg. subst.
  exists a1_1. di a0.
  Qed.

Lemma check_to_infer : forall G M a, check G M a = Some tt -> infer G M = Some a.
Proof.
  intros. generalize dependent a. generalize dependent G.
  induction M; intros.
  - cbn in *.
    ind_rem (guard (type_eq a typebool)) t Ht. di a0.
    apply from_guard_type_eq in Ht. subst. auto.
  - cbn in *.
    di (check G M1 typebool).
    ind_rem (check G M2 a) m2 Hm2. di a0.
    apply eq_sym in Hm2.
    apply IHM2 in Hm2 as Hcm2. 
    (* apply IHM3 in H. *)
    rewrite Hcm2. cbn. rewrite H. cbn. auto. 
  - cbn in *. di (lookup G v).
    ind_rem (guard (type_eq a t)) eqat Heq.
    di a0. apply from_guard_type_eq in Heq. subst. auto.
  - apply check_lam in H; destruct H as [b H]; destruct H as [Ha H].
    cbn.
    apply IHM in H. rewrite H. cbn. rewrite Ha. reflexivity.
  - apply check_app in H; destruct H as [b H]; destruct H as [Hi Hc].
    cbn. rewrite Hi. rewrite Hc. cbn. auto.
  Qed.

Lemma infer_lam : forall G v t M a, infer G (lam v t M) = Some a ->
  exists b, a = t ~> b /\ infer ((v, t) :: G) M = Some b.
Proof.
  intros.
  cbn in H.
  ind_rem (infer ((v, t) :: G) M) im Him.
  inversion H; subst; clear H.
  exists a0; auto.
  Qed.

Lemma infer_app : forall G M1 M2 a, infer G (M1 · M2) = Some a ->
  exists b, infer G M1 = Some (b ~> a) /\ check G M2 b = Some tt.
Proof.
  intros.
  ind_rem (infer G (M1 · M2)) im Him.
  ind_rem (infer G M1) im1 Him1.
  di a1.
  ind_rem (check G M2 a1_1) cm2 Hcm2.
  inversion H. inversion Him. subst. clear H Him.
  destruct a1.
  exists a1_1.
  auto.
  Qed.

Lemma infer_ok : forall G M a, infer G M = Some a -> has_type G M a.
Proof.
  intros. generalize dependent a. generalize dependent G.
  induction M; intros.
  - cbn in H. inversion H. constructor.
  - cbn in H.
    ind_rem (check G M1 typebool) cm1 Hcm1. di a0.
    ind_rem (infer G M2) im2 Him2.
    ind_rem (check G M3 a0) cm3 Hcm3. di a1.
    inversion H. subst. clear H.
    apply eq_sym in Hcm1. apply check_to_infer in Hcm1. apply IHM1 in Hcm1.
    apply eq_sym in Hcm3. apply check_to_infer in Hcm3. apply IHM3 in Hcm3.
    apply eq_sym in Him2. apply IHM2 in Him2.
    constructor; assumption.
  - constructor. cbn in H. auto.
  - apply infer_lam in H as H1; destruct H1 as [ b H1 ];
      destruct H1 as [H0 H1]; rewrite H0 in *; clear H0.
    constructor.
    apply IHM.
    assumption.
  - apply infer_app in H as H1; 
      destruct H1 as [b H1]; destruct H1 as [H1 H2].
    apply app_has_type with b.
    + apply IHM1. assumption.
    + apply check_to_infer in H2. apply IHM2. auto.
  Qed.

Definition typecheck (G : ctx) (M : term) : option { A : type | has_type G M A }.
  ind_rem (infer G M) o H.
  - refine (Some (exist _ a _)).
    apply infer_ok. auto.
  - refine None.
Defined.

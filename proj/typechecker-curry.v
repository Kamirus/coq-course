
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
(* | typevar : var -> type *)
| typelam : type -> type -> type
.
Notation "a ~> b" :=
  (typelam a b)
  (at level 62, right associativity)
.

Notation "'[' a ',' b ']' <-~ A ; B" :=
  ( match A with
    | Some (a ~> b) => B
    | _ => None
    end
  )
  (right associativity, at level 60).

Fixpoint type_eq (a b : type) : bool :=
  match a, b with
  | typebool, typebool => true
  (* | typevar x, typevar y => if string_dec x y then true else false *)
  | a1 ~> a2, b1 ~> b2 => andb (type_eq a1 b1) (type_eq a2 b2)
  | _, _ => false
  end
.
Inductive term :=
| termbool : bool -> term
(* | termif : term -> term -> term -> term *)
| termvar : var -> term
| lam : var -> term -> term
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
| bool_has_type : forall G b, has_type G (termbool b) typebool
(* | if_has_type : forall G b c1 c2 a,
  has_type G b typebool ->
  has_type G c1 a -> 
  has_type G c2 a -> 
  has_type G (termif b c1 c2) a *)
| var_has_type : forall G x a, lookup G x = Some a -> has_type G (termvar x) a
| lam_has_type : forall G x M (a b : type),
  has_type ((x, b) :: G) M a ->
  has_type G (lam x M) (b ~> a)
| app_has_type : forall G (M N : term) (a b : type),
  has_type G M (a ~> b) -> has_type G N a -> has_type G (M · N) b
.
Hint Constructors has_type term type.

Inductive iterm :=
| itermbool : bool -> iterm
(* | itermif : cterm -> cterm -> cterm -> iterm *)
| itermvar : var -> iterm
| ilam : var -> cterm -> iterm
| itermapp : cterm -> cterm -> iterm
with cterm :=
| C : iterm -> cterm
.

Print iterm.

Fixpoint term_to_iterm M :=
  let I x := C (term_to_iterm x) in
  match M with
  | termbool b => itermbool b
  (* | termif b c1 c2 => itermif (I b) (I c1) (I c2) *)
  | termvar x => itermvar x
  | lam x N => ilam x (I N)
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
  | itermbool b => termbool b
  (* | itermif (C b) (C c1) (C c2) => termif (T b) (T c1) (T c2) *)
  | itermvar x => termvar x
  | ilam x cN => lam x (T cN)
  | itermapp cM1 cM2 => (T cM1) · (T cM2)
  end
.

Fixpoint infer (G : ctx) (M : iterm) : option type :=
  match M with
  | itermbool _ => ret typebool
  (* | itermif cb (C c1) cc2 =>
    check G cb typebool ;;
    a <-- infer G c1 ;
    check G cc2 a ;;
    ret a *)
  | itermvar x => lookup G x
  | ilam x (C N) => None
  | itermapp (C M1) cM2 => 
    [a, b] <-~ infer G M1 ;
    check G cM2 a ;;
    ret b
  end
with check (G : ctx) (M : cterm) (A : type) : option unit :=
  match M with
  | C (ilam x N) => 
    [a, b] <-~ Some A ;
    check ((x, a) :: G) N b
  | C (itermapp cM1 (C M2)) =>
    (* try to infer argument, and then check function *)
    match infer G M2 with
    | Some a => 
      check G cM1 (a ~> A)
    | None => 
      (* default as below *)
      a <-- infer G (unC M) ;
      guard (type_eq A a)
    end
  | C M => 
    a <-- infer G M ;
    guard (type_eq A a)
  end
.

Definition vx := termvar "x"%string.
Definition vy := termvar "y"%string.
Definition vz := termvar "z"%string.
Definition lam_cons_bool := lam "x"%string (termbool true).
Compute infer nil (term_to_iterm lam_cons_bool).
Compute check nil (C (term_to_iterm lam_cons_bool)) (typebool ~> typebool).

Lemma from_guard_type_eq : forall a b, guard (type_eq a b) = Some tt -> a = b.
Proof.
  intros.
  generalize dependent b. induction a; intros.
  { ind_rem (type_eq typebool b) t Ht. di b. } 
  (* { ind_rem (type_eq (typevar v) b) t Ht. di b. di (string_dec v v0). } *)
  { ind_rem (type_eq (a1 ~> a2) b) t Ht. di b. cbn in *.
    ind_rem (type_eq a1 b1) t1 Ht1. cbn in *.
    assert (guard (type_eq a1 b1) = Some tt). rewrite <- Ht1; auto.
    assert (guard (type_eq a2 b2) = Some tt). rewrite <- Ht; auto.
    rewrite IHa1 with b1; auto.
    rewrite IHa2 with b2; auto.
  }
  Qed.
Hint Rewrite from_guard_type_eq.
Hint Resolve from_guard_type_eq.

Lemma infer_check_prim : forall M G A,
  (infer G (term_to_iterm M) = Some A
  \/ check G (C (term_to_iterm M)) A = Some tt) ->
  has_type G M A.
Proof.
  intros. generalize dependent G. generalize dependent A.
  induction M; intros.
  - destruct H; cbn in *.
    inversion H. constructor.
    assert (A = typebool); auto. subst. constructor.
  - destruct H; cbn in *.
    constructor. auto.
    ind_rem (lookup G v) a Ha. constructor. 
    apply from_guard_type_eq in H. subst. auto.
  - destruct H; cbn in H; try_inv.
    destruct A. inversion H.
    auto.
  - destruct H; cbn in H.
    + 
      ind_rem (infer G (term_to_iterm M1)) im1 Him1.
      di a.
      ind_rem (
        match term_to_iterm M2 with
        | itermbool _ => a <-- infer G (term_to_iterm M2); guard (type_eq a1 a)
        | itermvar _ => a <-- infer G (term_to_iterm M2); guard (type_eq a1 a)
        | ilam x N =>
            match a1 with
            | typebool => None
            | a ~> b => check ((x, a) :: G) N b
            end
        | itermapp cM1 c =>
            match c with
            | C M3 =>
                match infer G M3 with
                | Some a => check G cM1 (a ~> a1)
                | None => a <-- infer G (term_to_iterm M2); guard (type_eq a1 a)
                end
            end
        end
      ) cm2 Hcm2. cbn in *. inversion H. subst. clear H.
      apply eq_sym in Hcm2.
      eapply or_intror in Hcm2. di a. eapply IHM2 in Hcm2.
      apply eq_sym in Him1.
      eapply or_introl in Him1. eapply IHM1 in Him1.
      eapply app_has_type; eauto.
    + ind_rem (infer G (term_to_iterm M2)) im2 Him2.
      eapply or_intror in H.
      eapply IHM1 in H.
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

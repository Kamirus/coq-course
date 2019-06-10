
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
  (* cbn in *; *)
  try_inv.

Ltac di h := destruct h; try_inv.

(* main *)

Definition var := string.
(*
Eval compute in (if string_dec "a" "b" then 1 else 2). (* porównanie napisów *)
Eval compute in (if string_dec "a" "a" then 1 else 2). (* porównanie napisów *)
*)

Inductive type :=
| typebool : type
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
  | a1 ~> a2, b1 ~> b2 => andb (type_eq a1 b1) (type_eq a2 b2)
  | _, _ => false
  end
.
Inductive term :=
| termbool : bool -> term
| termif : term -> term -> term -> term
| termann : term -> type -> term
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
| if_has_type : forall G b c1 c2 a,
  has_type G b typebool ->
  has_type G c1 a -> 
  has_type G c2 a -> 
  has_type G (termif b c1 c2) a
| ann_has_type : forall G M a,
  has_type G M a ->
  has_type G (termann M a) a
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
| itermif : cterm -> cterm -> cterm -> iterm
| itermann : cterm -> type -> iterm
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
  | termif b c1 c2 => itermif (I b) (I c1) (I c2)
  | termann M a => itermann (I M) a
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
  | itermif b c1 c2 => termif (T b) (T c1) (T c2)
  | itermann M a => termann (T M) a
  | itermvar x => termvar x
  | ilam x cN => lam x (T cN)
  | itermapp cM1 cM2 => (T cM1) · (T cM2)
  end
.

Fixpoint infer (G : ctx) (M : iterm) : option type :=
  match M with
  | itermbool _ => ret typebool
  | itermif cb (C c1) cc2 =>
    check G cb typebool ;;
    a <-- infer G c1 ;
    check G cc2 a ;;
    ret a
  | itermann cN a => 
    check G cN a ;;
    ret a
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

Lemma unfold_infer_app : forall M1 M2 G,
  infer G (term_to_iterm (M1 · M2)) = 
    [a, b] <-~ infer G (term_to_iterm M1) ;
    check G (C (term_to_iterm M2)) a ;;
    ret b.
Proof. auto. Qed.

Lemma unfold_check_app : forall G M1 M2 A,
  check G (C (term_to_iterm (M1 · M2))) A =
    match infer G (term_to_iterm M2) with
    | Some a => 
      check G (C (term_to_iterm M1)) (a ~> A)
    | None => 
      (* default as below *)
      a <-- infer G (term_to_iterm (M1 · M2)) ;
      guard (type_eq A a)
    end.
Proof. auto. Qed.

Lemma unfold_infer_if : forall G M1 M2 M3,
  infer G (term_to_iterm (termif M1 M2 M3)) = 
    check G (C (term_to_iterm M1)) typebool ;;
    a <-- infer G (term_to_iterm M2) ;
    check G (C (term_to_iterm M3)) a ;;
    ret a.
Proof. auto. Qed.

Lemma unfold_check_if : forall G M1 M2 M3 A,
  check G (C (term_to_iterm (termif M1 M2 M3))) A = 
    a <-- infer G ((term_to_iterm (termif M1 M2 M3))) ;
    guard (type_eq A a).
Proof. auto. Qed.

Ltac app IH H := 
  (apply eq_sym in H + idtac);
  (eapply or_introl in H + eapply or_intror in H + idtac);
  eapply IH in H.

Ltac fold_cbn t H :=
  let o := fresh "o" in
  let Ho := fresh "Ho" in
  let H0 := fresh "H0" in
  remember t as o eqn:Ho;
  cbn in H; 
  inversion Ho as [ H0 ]; cbn in Ho;
  rewrite <- Ho in H; rewrite H0 in H;
  clear o Ho H0.

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
  - rewrite unfold_check_if in H.
    rewrite unfold_infer_if in H.
    destruct H;
    ind_rem (check G (C (term_to_iterm M1)) typebool) m1 Hm1; di a;
    ind_rem (infer G (term_to_iterm M2)) m2 Hm2;
    fold_cbn (check G (C (term_to_iterm M3)) a) H;
    ind_rem (check G (C (term_to_iterm M3)) a) m3 Hm3;
    cbn in H; inversion H; subst; di a0.
    apply from_guard_type_eq in H. subst. auto.
  - destruct H;
    fold_cbn (check G (C (term_to_iterm M)) t) H;
    ind_rem (check G (C (term_to_iterm M)) t) m Hm;
    cbn in H; inversion H; subst; clear H; di a.
      apply from_guard_type_eq in H1. subst. auto.
  - destruct H; cbn in *.
    constructor. auto.
    ind_rem (lookup G v) a Ha. constructor. 
    apply from_guard_type_eq in H. subst. auto.
  - destruct H; cbn in H; try_inv.
    destruct A. inversion H.
    auto.
  - destruct H.
    + rewrite unfold_infer_app in H.
      ind_rem (infer G (term_to_iterm M1)) im1 Him1. di a.
      ind_rem (check G (C (term_to_iterm M2)) a1) cm2 Hcm2.
      cbn in H. inversion H. subst. clear H. di a.
      app IHM1 Him1.
      app IHM2 Hcm2.
      econstructor; eauto.
    + rewrite unfold_check_app in H.
      ind_rem (infer G (term_to_iterm M2)) m2 Hm2.
      { app IHM2 Hm2. app IHM1 H. econstructor; eauto. }
      { ind_rem (infer G (term_to_iterm (M1 · M2))) m Hm.
        cbn in H. apply from_guard_type_eq in H. subst.
        rename Hm into H. rename a into A. apply eq_sym in H.
        (* duplicate 1st plus case *)
        rewrite unfold_infer_app in H.
        ind_rem (infer G (term_to_iterm M1)) im1 Him1. di a.
        ind_rem (check G (C (term_to_iterm M2)) a1) cm2 Hcm2.
        cbn in H. inversion H. subst. clear H. di a.
        app IHM1 Him1.
        app IHM2 Hcm2.
        econstructor; eauto.
      }
  Qed.

Definition Infer G M : option { A : type | has_type G M A }.
  ind_rem (infer G (term_to_iterm M)) m Hm.
  - apply Some. econstructor. app infer_check_prim Hm. eauto.
  - apply None.
Defined.

Print Infer.

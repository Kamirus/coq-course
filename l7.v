Require Import Arith.

Search ({_ <= _} + {_ < _}). (* le_gt_dec *)
Print le_lt_dec.

Definition ret {A : Type} (x : A) := Some x.
 
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.
Hint Unfold ret bind.

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
Load DepList.

Definition Env len := ilist Q len.
(* b) Define a function lookup for reading an element out of a list of rationals,
by its position in the list. *)
Fixpoint lookup (len : nat) (i : nat) (env : Env len) := 
  match i, env with
  | _, INil => 0
  | O, ICons _ x _ => x
  | (S i')%nat, ICons _ x env' => lookup i' env'
  end
.
Hint Unfold lookup.
(* List.nth i env 0. *)

(* c) Define a function expDenote that translates exps,
along with lists of rationals representing variable values, to Q . *)
Fixpoint expDenote (len : nat) (e : exp) (env : Env len) : Q :=
  match e with
  | var x => lookup x env
  | const a => a
  | add e1 e2 => expDenote e1 env + expDenote e2 env
  | sub e1 e2 => expDenote e1 env - expDenote e2 env
  | mul e1 e2 => expDenote e1 env * expDenote e2 env
  end
.

(* d) Define a recursive function eqsDenote over list ( exp × Q ),
characterizing when all of the equations are true. *)
Fixpoint eqsDenote len (env : Env len) (es : list (exp * Q)) :=
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
  | mul (const c) e => linearize (c * k) e len
  | mul e (const c) => linearize (c * k) e len
  | mul _ _ => None
  (* | mul e1 e2 => match toConst e1, toConst e2 with
                | Some c1, None => linearize (c1 * k) e2 len
                | None, Some c2 => linearize (c2 * k) e1 len
                | _, _ => None
                end *)
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

Fixpoint lhsDenote len (l : lhs len) : Env len -> Q :=
  match l with
  | INil => fun _ => 0
  | ICons n a l' => fun env => lookup 0 env * a + lhsDenote l' (tl env)
  end
.

Hint Resolve Qmult_0_r.

Ltac try_inv :=
  match goal with
  | [ H : _ |- _ ] => solve [inversion H; auto]
  | _ => idtac
  end.

Ltac induction_rem h b Hb :=
  remember h as b eqn:Hb; apply eq_sym in Hb; dependent induction b; cbn in *;
  try_inv.

Ltac ind h :=
  dependent induction h; cbn in *; try_inv.

Ltac dd h := dependent destruction h.

Ltac dind h :=
  dependent induction h; try_inv.

Ltac auto2 := auto; auto with arith; auto with qarith.

Require Import Coq.Program.Equality.

Lemma denoteEvery0 : forall len env,
  lhsDenote env (everywhere 0 len) == 0.
Proof.
  intros. dind len; cbn; dd env; cbn; auto with qarith.
  rewrite IHlen. auto with qarith.
  Qed.
Hint Rewrite denoteEvery0.

Hint Resolve Qplus_0_r Qmult_comm Qmult_0_l Qplus_0_l.
Search (0 * _ == 0).

Lemma denoteSingle : forall n len (env : Env len) q, (n < len)%nat ->
  lhsDenote env (singleton q 0 len n) == lookup n env * q.
Proof.
  intros. dind n; dind len; cbn; dd env; cbn.
  - rewrite denoteEvery0. rewrite Qplus_0_r. auto with qarith.
  - rewrite IHn; auto with arith.
    rewrite Qmult_0_l. auto with qarith.
  Qed.
Hint Resolve denoteSingle.
Hint Rewrite denoteSingle.

Lemma denoteSingleOut : forall n len (env : Env len) q, (n >= len)%nat ->
  lhsDenote env (singleton q 0 len n) == 0.
Proof.
  intros. dind n; dind len; cbn; dd env; cbn; auto2.
  rewrite Qmult_0_l. rewrite Qplus_0_l. apply IHn. auto2.
  Qed.

Lemma lookupOut : forall n len (env : Env len), (n >= len)%nat -> lookup n env == 0.
Proof.
  intros. dind n; dd env; cbn; auto2; try_inv.
  Qed.

Hint Rewrite Qmult_plus_distr_l.
Check Qplus_assoc.

Lemma map2_aux : forall q0 q1 q a b, 
  (q0 + q1) * q + (a + b) == q0 * q + a + (q1 * q + b).
Proof. intros. ring. Qed.
Hint Resolve map2_aux.

Lemma map2_ok : forall len (env : Env len) (a b : lhs len),
  lhsDenote env (map2 Qplus a b) == lhsDenote env a + lhsDenote env b.
Proof.
  intros.
  dind len; dd a; dd b; dd env; cbn; auto2.
  rewrite IHlen. auto.
  Qed.

Lemma map2_ok_minus : forall len (env : Env len) (a b : lhs len),
  lhsDenote env (map2 Qminus a b) == lhsDenote env a + - lhsDenote env b.
Proof.
  intros.
  dind len; dd a; dd b; dd env; cbn; auto2.
  rewrite IHlen. 
  ring.
  Qed.

Lemma Qmul_minus_aux : forall a b k, a == k * b -> - a == k * (- b).
Proof. intros. rewrite H. ring. Qed.

Ltac case_le_lt_dec len n := 
  case (le_lt_dec len n); intros;
  (rewrite lookupOut; auto2; rewrite denoteSingleOut; auto2; ring)
  || (rewrite denoteSingle; auto; ring).

(* i) Prove: when exp linearization succeeds on constant k and expression e,
the linearized version has the same meaning as k × e. *)
Lemma lin_ok : forall e len lhs k,
  linearize k e len = Some lhs -> forall env, 
  lhsDenote env lhs == k * expDenote e env.
  intro.
  dind e; intros; cbn in *.
  - inversion H. case_le_lt_dec len n.
  - inversion H.
  - induction_rem (linearize k e1 len) o1 Ho1.
    induction_rem (linearize k e2 len) o2 Ho2.
    rewrite Qmult_plus_distr_r.
    eapply IHe1 in Ho1. rewrite <- Ho1.
    eapply IHe2 in Ho2. rewrite <- Ho2.
    inversion H.
    apply map2_ok.
  - induction_rem (linearize k e1 len) o1 Ho1.
    induction_rem (linearize k e2 len) o2 Ho2.
    unfold Qminus.
    rewrite Qmult_plus_distr_r.
    eapply IHe1 in Ho1. rewrite <- Ho1.
    eapply IHe2 in Ho2. 
      assert (forall a b k, a == k * b -> - a == k * (- b)).
      intros aa bb kk Hh; rewrite Hh; ring. 
    apply H0 in Ho2. rewrite <- Ho2.
    inversion H.
    apply map2_ok_minus.
  - dd e1; try solve
      [dd e2; cbn in *; try_inv; eapply IHe1 in H; rewrite H; ring].
    cbn in *; try_inv; solve [eapply IHe2 in H; rewrite H; ring].
Qed.

(* j) Prove: when linearizeEqs succeeds on an equation list eqs,
then the final summed-up equation is true whenever
the original equation list is true. *)

(* k) Write a tactic findVarsHyps to search through all equalities on rationals
in the context, recursing through addition, subtraction, and multiplication
to find the list of expressions that should be treated as variables.
This list should be suitable as an argument to expDenote and eqsDenote,
associating a Q value to each natural number that stands for a variable. *)
(* Ltac findVarsHyps  *)

(* l) Write a tactic reify to reify a Q expression into exp,
with respect to a given list of variable values. *)

(* m) Write a tactic reifyEqs to reify a formula that begins with a sequence of
implications from linear equalities whose lefthand sides are expressed with
expDenote. This tactic should build a list (exp × Q) representing the equations.
Remember to give an explicit type annotation when returning a nil list,
as in constr :(@ nil(exp × Q)). *)

(* n) Now this final tactic should do the job: *)

Ltac reifyContext :=
  let ls := findVarsHyps in
  repeat match goal with
    | [ H : ?e == ?num # ?den |- _ ] ⇒
      let r := reify ls e in
      change (expDenote ls r == num # den) in H;
      generalize H
    end;
  match goal with
  | [ |- ?g ] ⇒
    let re := reifyEqs g in
    intros;
    let H := fresh "H" in
    assert (H : eqsDenote ls re);
    [ simpl in *; tauto
      | repeat match goal with
  == |- ] ⇒ clear H
  | [ H : expDenote
  end ;
  end.
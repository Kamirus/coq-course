(* Copyright (c) 2008-2012, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)


Require Import List.

Require Import CpdtTactics MoreSpecif.

Set Implicit Arguments.


(** * A Smarter Tautology Solver *)

Require Import Quote.

Inductive formula : Set :=
| Atomic : index -> formula
| Truth : formula
| Falsehood : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imp : formula -> formula -> formula.


Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).

(** Now we can define our denotation function. *)

Definition asgn := varmap Prop.
Print varmap.
Print index.
Check varmap_find.

Fixpoint formulaDenote (atomics : asgn) (f : formula) : Prop :=
  match f with
    | Atomic v => varmap_find False v atomics
    | Truth => True
    | Falsehood => False
    | And f1 f2 => formulaDenote atomics f1 /\ formulaDenote atomics f2
    | Or f1 f2 => formulaDenote atomics f1 \/ formulaDenote atomics f2
    | Imp f1 f2 => formulaDenote atomics f1 --> formulaDenote atomics f2
  end.

Goal 
forall A B:Prop, True /\ (True \/ False) /\ A --> B /\ B.
intros.
quote formulaDenote.
Abort.

Section my_tauto.
  Variable atomics : asgn.

  Definition holds (v : index) := varmap_find False v atomics.

  Require Import ListSet.

  Definition index_eq : forall x y : index, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition add (s : set index) (v : index) := set_add index_eq v s.

  Definition In_dec : forall v (s : set index), {In v s} + {~ In v s}.
  Local Open Scope specif_scope.
    intro; refine (fix F (s : set index) : {In v s} + {~ In v s} :=
      match s with
        | nil => No
        | v' :: s' => index_eq v' v || F s'
      end); crush.
  Defined.


  Fixpoint allTrue (s : set index) : Prop :=
    match s with
      | nil => True
      | v :: s' => holds v /\ allTrue s'
    end.

  Theorem allTrue_add : forall v s,
    allTrue s
    -> holds v
    -> allTrue (add s v).
    induction s; crush;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; crush.
  Qed.

  Theorem allTrue_In : forall v s,
    allTrue s
    -> set_In v s
    -> varmap_find False v atomics.
    induction s; crush.
  Qed.

  Hint Resolve allTrue_add allTrue_In.

  Local Open Scope partial_scope.

  Definition forward : forall (f : formula) (known : set index) (hyp : formula)
    (cont : forall known', [allTrue known' -> formulaDenote atomics f]),
    [allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f].
    
    refine (fix F (f : formula) (known : set index) (hyp : formula)
      (cont : forall known', [allTrue known' -> formulaDenote atomics f])
      : [allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f] :=
      
      match hyp with
        | Atomic v => Reduce (cont (add known v))
        | Truth => Reduce (cont known)
        | Falsehood => Yes
        | And h1 h2 =>
          Reduce (F (Imp h2 f) known h1 (fun known' =>
            Reduce (F f known' h2 cont)))
        | Or h1 h2 => F f known h1 cont && F f known h2 cont
        | Imp _ _ => Reduce (cont known)
      end); crush.
  Defined.

  Definition backward : forall (known : set index) (f : formula),
    [allTrue known -> formulaDenote atomics f].
    refine (fix F (known : set index) (f : formula)
      : [allTrue known -> formulaDenote atomics f] :=
      match f with
        | Atomic v => Reduce (In_dec v known)
        | Truth => Yes
        | Falsehood => No
        | And f1 f2 => F known f1 && F known f2
        | Or f1 f2 => F known f1 || F known f2
        | Imp f1 f2 => forward f2 known f1 (fun known' => F known' f2)
      end); crush; eauto.
  Defined.


  Definition my_tauto : forall f : formula, [formulaDenote atomics f].

    intro; refine (Reduce (backward nil f)); crush.
  Defined.

End my_tauto.

Definition get_form {P} (x: partial P) :=
match x with
| Proved p => P
| _ => True
end.

Definition get_proof {P} (x:partial P) : get_form x :=
match x with
| Proved p => p
| _ => I
end.

Ltac my_tauto :=
  repeat match goal with
           | [ |- forall x : ?P, _ ] =>
             match type of P with
               | Prop => fail 1
               | _ => intro
             end
         end;
  quote formulaDenote;
  match goal with
    | [ |- formulaDenote ?m ?f ] => exact (get_proof (my_tauto m f))
  end.


Theorem mt1 : True.
  my_tauto.
Qed.

Print mt1.

Theorem mt2 : forall x y : nat, x = y --> x = y.
  my_tauto.
Qed.

Print mt2.

Theorem mt3 : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  --> y > z /\ (x < y \/ x < S y).
  my_tauto.
Qed.

Print mt3.

Theorem mt4 : True /\ True /\ True /\ True /\ True /\ True /\ False --> False.
  my_tauto.
Qed.

Print mt4.


Theorem mt4' : True /\ True /\ True /\ True /\ True /\ True /\ False -> False.
  tauto.
Qed.

Print mt4'.

(* Without quote: *)

Ltac inList x xs :=
  match xs with
    | tt => false
    | (x, _) => true
    | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
    match b with
      | true => xs
      | false => constr:((x, xs))
    end.

(** Now we can write our recursive function to calculate the list of variable values we will want to use to represent a term. *)

Ltac allVars xs e :=
  match e with
    | True => xs
    | False => xs
    | ?e1 /\ ?e2 =>
      let xs := allVars xs e1 in
        allVars xs e2
    | ?e1 \/ ?e2 =>
      let xs := allVars xs e1 in
        allVars xs e2
    | ?e1 -> ?e2 =>
      let xs := allVars xs e1 in
        allVars xs e2
    | _ => addToList e xs
  end.

(** We will also need a way to map a value to its position in a list. *)

Ltac lookup x xs :=
  match xs with
    | (x, _) => O
    | (_, ?xs') =>
      let n := lookup x xs' in
        constr:(S n)
  end.

(** The next building block is a procedure for reifying a term, given a list of all allowed variable values.  We are free to make this procedure partial, where tactic failure may be triggered upon attempting to reflect a term containing subterms not included in the list of variables.  The output type of the term is a copy of [formula] where [index] is replaced by [nat], in the type of the constructor for atomic formulas. *)

Inductive formula' : Set :=
| Atomic' : nat -> formula'
| Truth' : formula'
| Falsehood' : formula'
| And' : formula' -> formula' -> formula'
| Or' : formula' -> formula' -> formula'
| Imp' : formula' -> formula' -> formula'.

(** Note that, when we write our own Ltac procedure, we can work directly with the normal [->] operator, rather than needing to introduce a wrapper for it. *)

Ltac reifyTerm xs e :=
  match e with
    | True => Truth'
    | False => Falsehood'
    | ?e1 /\ ?e2 =>
      let p1 := reifyTerm xs e1 in
      let p2 := reifyTerm xs e2 in
        constr:(And' p1 p2)
    | ?e1 \/ ?e2 =>
      let p1 := reifyTerm xs e1 in
      let p2 := reifyTerm xs e2 in
        constr:(Or' p1 p2)
    | ?e1 -> ?e2 =>
      let p1 := reifyTerm xs e1 in
      let p2 := reifyTerm xs e2 in
        constr:(Imp' p1 p2)
    | _ =>
      let n := lookup e xs in
        constr:(Atomic' n)
  end.

(** Finally, we bring all the pieces together. *)

Ltac reify :=
  match goal with
    | [ |- ?G ] => let xs := allVars tt G in
      let p := reifyTerm xs G in
        pose p
  end.

(** A quick test verifies that we are doing reification correctly. *)

Theorem mt3' : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  -> y > z /\ (x < y \/ x < S y).
  do 3 intro.
  reify.
Abort.

(** More work would be needed to complete the reflective tactic, as we must connect our new syntax type with the real meanings of formulas, but the details are the same as in our prior implementation with [quote]. *)

(** * Building a Reification Tactic that Recurses Under Binders *)

(** All of our examples so far have stayed away from reifying the syntax of terms that use such features as quantifiers and [fun] function abstractions.  Such cases are complicated by the fact that different subterms may be allowed to reference different sets of free variables.  Some cleverness is needed to clear this hurdle, but a few simple patterns will suffice.  Consider this example of a simple dependently typed term language, where a function abstraction body is represented conveniently with a Coq function. *)

Inductive type : Type :=
| Nat : type
| NatFunc : type -> type.

Inductive term : type -> Type :=
| Const : nat -> term Nat
| Plus : term Nat -> term Nat -> term Nat
| Abs : forall t, (nat -> term t) -> term (NatFunc t).

Fixpoint typeDenote (t : type) : Type :=
  match t with
    | Nat => nat
    | NatFunc t => nat -> typeDenote t
  end.

Fixpoint termDenote t (e : term t) : typeDenote t :=
  match e with
    | Const n => n
    | Plus e1 e2 => termDenote e1 + termDenote e2
    | Abs e1 => fun x => termDenote (e1 x)
  end.

(** Here is a naive first attempt at a reification tactic. *)

Ltac refl0 e :=
  match e with
    | ?E1 + ?E2 =>
      let r1 := refl0 E1 in
      let r2 := refl0 E2 in
        constr:(Plus r1 r2)

    | fun x : nat => ?E1 =>
      let r1 := refl0 E1 in
        constr:(Abs (fun x => r1 x))

    | _ => constr:(Const e)
  end.


(** Recall that a regular Ltac pattern variable [?X] only matches terms that %\emph{%#<i>#do not mention new variables introduced within the pattern#</i>#%}%.  In our naive implementation, the case for matching function abstractions matches the function body in a way that prevents it from mentioning the function argument!  Our code above plays fast and loose with the function body in a way that leads to independent problems, but we could change the code so that it indeed handles function abstractions that ignore their arguments.

   To handle functions in general, we will use the pattern variable form [@?X], which allows [X] to mention newly introduced variables that are declared explicitly.  For instance: *)

Ltac refl1 e :=
  match e with
    | ?E1 + ?E2 =>
      let r1 := refl1 E1 in
      let r2 := refl1 E2 in
        constr:(Plus r1 r2)

    | fun x : nat => @?E1 x =>
      let r1 := refl1 E1 in
        constr:(Abs r1)

    | _ => constr:(Const e)
  end.

Ltac test e :=
match e with
| fun x : nat => @?E1 x =>
let q :=E1 in idtac q
end.


(** Now, in the abstraction case, we bind [E1] as a function from an [x] value to the value of the abstraction body.  Unfortunately, our recursive call there is not destined for success.  It will match the same abstraction pattern and trigger another recursive call, and so on through infinite recursion.  One last refactoring yields a working procedure.  The key idea is to consider every input to [refl'] as %\emph{%#<i>#a function over the values of variables introduced during recursion#</i>#%}%. *)

Ltac refl' e :=
  match eval simpl in e with
    | fun x : ?T => @?E1 x + @?E2 x =>
      let r1 := refl' E1 in
      let r2 := refl' E2 in
        constr:(fun x => Plus (r1 x) (r2 x))

    | fun (x : ?T) (y : nat) => @?E1 x y =>
      let r1 := refl' (fun p : T * nat => E1 (fst p) (snd p)) in
        constr:(fun x => Abs (fun y => r1 (x, y)))

    | _ => constr:(fun x => Const (e x))
  end.

(** Note how now even the addition case works in terms of functions, with [@?X] patterns.  The abstraction case introduces a new variable by extending the type used to represent the free variables.  In particular, the argument to [refl'] used type [T] to represent all free variables.  We extend the type to [T * nat] for the type representing free variable values within the abstraction body.  A bit of bookkeeping with pairs and their projections produces an appropriate version of the abstraction body to pass in a recursive call.  To ensure that all this repackaging of terms does not interfere with pattern matching, we add an extra [simpl] reduction on the function argument, in the first line of the body of [refl'].

   Now one more tactic provides an example of how to apply reification.  Let us consider goals that are equalities between terms that can be reified.  We want to change such goals into equalities between appropriate calls to [termDenote]. *)

Ltac refl :=
  match goal with
    | [ |- ?E1 = ?E2 ] =>
      let E1' := refl' (fun _ : unit => E1) in
      let E2' := refl' (fun _ : unit => E2) in
        change (termDenote (E1' tt) = termDenote (E2' tt));
          cbv beta iota delta [fst snd]
  end.

Goal (fun (x y : nat) => x + y + 13) = (fun (_ z : nat) => z).
  refl.
Abort.


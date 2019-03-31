Require Import List.
Require Extraction.

Notation "[]" := nil : myscope.
Infix "::" := cons (at level 60, right associativity) : myscope.

Open Scope myscope.

Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : myscope.

(* Specyfikacje i typy podzbiorowe *)

(* slaba specyfikacja funkcji : definicja + tw. o poprawnosci *)

Definition tail {A} (l:list A) : list A :=
match l with
| [] => []
| h::t => t
end.

Lemma tail_spec0 :
forall A l, l <> [] -> exists x:A, x::tail l = l.
Proof.
induction l; auto; intros H; [ elim H | idtac ]; eauto.
Qed. 

Extraction tail.

(* inaczej: *)

Definition tail1 {A} (l:list A) : l <> [] -> list A :=
match l (* return l <> [] -> list A *) with
| [] => fun p => match (p (refl_equal [])) with end
| h::t => fun _ => t
end.

Eval compute in tail1 [].
Eval compute in tail1 [3;4].
Eval compute in tail1 [3;4] _.
Eval compute in tail1 [] _.

(*Extraction Language Haskell. *)
Extraction tail1.

Hint Extern 1 =>
match goal with
| [ H : ?X <> ?X |- _ ] => elim H; trivial
| [ H : _::_ = [] |- _ ] => discriminate
end.
 
Lemma nil_not_nil_F :
forall {A} P, @nil A <> @nil A -> P.
Proof. auto. Qed.

Definition tail2 {A} (l:list A) : l <> [] -> list A :=
match l (* return l <> [] -> list A *) with
| [] => fun p => nil_not_nil_F _ p
| h::t => fun _ => t
end.


Extraction tail2.
Extraction nil_not_nil_F.

(*tak nie mozna: 
Definition tail3 A (l:list A) (p: l <> []) : list A :=
match l in list _ return list A with
| [] => nil_not_nil_F _ p
| h::t => t
end.
*)

Definition tail3 {A} (l:list A) : l <> [] -> list A.
generalize l; clear l.
refine (fun l =>
match l in list _ return l <> [] -> list A with
| [] => fun p => _
| h::t => fun _ => t
end).
elim p; trivial.
Defined.

Extraction tail3.


(* typ sig do definiowania silnej specyfikacji funkcji *)
Print ex.
Print sig.

Locate "{ _ : _ | _ }".

Definition tail_spec1 {A} (s : { l0 : list A | l0 <> []}) : list A :=
match s with
| exist _ [] p => match p (refl_equal []) with end
| exist _ (h::t) _ => t
end.

(*
Lemma two_not_nil : [2] <> [].
Proof. auto. Qed.
*)

Eval compute in tail_spec1 (exist _ [2] _).

Extraction tail_spec1.

Extraction sig.

Print proj1_sig.
Print proj2_sig.

Definition tail_spec2 {A} (s : { l0 : list A | l0 <> []}) : 
{ l' : list A | exists x:A, x :: l' = proj1_sig s} :=

match s (*return { l' : list A | exists x:A, cons x l' = proj1_sig s} *) with
| exist _ [] p => match p (refl_equal []) with end
| exist _ (h::t) p => exist _ t (ex_intro _ h (refl_equal (h :: t))) 
end.

Extraction tail_spec2.

Definition tail_spec3 : forall {A} l, l <> [] -> 
{ l' : list A | exists x:A, x :: l' = l}.
refine (fun {A} l =>
match l (* return { l' : list A | exists x:A, x :: l' = l} *) with
| [] => fun _ => _
| h::t => fun _ => exist _ t _
end). 
elim n; trivial.
split with h; trivial.
Defined.


Print tail_spec3.

Extraction tail_spec3.

Notation " ! " := (False_rect _ _) : spec_scope.
Notation " 'ret' x " := (exist _ x _) (at level 56, no associativity) : spec_scope.

Open Scope spec_scope.

Definition tail_spec4 : forall  {A} (l : list A), l <> [] ->
 { l' : list A | exists x:A, x :: l' = l}.
refine (fun {A} l =>
match l with
| [] => fun _ => !
| h::t => fun _ => ret t
end); eauto.
Defined.

Print tail_spec4.
Eval compute in tail_spec4 [4;5] _.
Extraction tail_spec4.

Require Program.

Obligation Tactic := eauto.

Program Definition tail_spec_program {A} (l : list A) : l <> [] -> 
{ l' : list A | exists x:A, x :: l' = l} :=
match l with
| [] => fun _ => !
| h::t => fun _ => ret t
end.


Obligation 2.
intros; 
split with h; auto.
Qed.

Print tail_spec_program.
Extraction tail_spec_program.


(* czes\u009bciowe typy podzbiorowe *)

Inductive options {A:Type} (P : A -> Prop) : Type :=
| No : options P 
| Yes : forall x:A, P x -> options P.

Extraction options.

Notation "{{ x | P }}" := (options (fun x => P)) : option_scope.
Notation "[[ x ]]" := (Yes _ x _) : option_scope.
Notation "!!" := (No _) : option_scope.

Open Scope option_scope.

Definition tail5 : forall {A} (l:list A), {{ l0 | exists x:A, x::l0 = l}}.
refine (fun {A} l =>
match l (*return {{l0 | exists x:A, x::l0 = l}} *) with
| [] => !!
| h::t => [[ t ]]
end).
eauto.
Defined.

Print tail5.

Eval compute in tail5 [2;3;4].
Extraction options.
Extraction tail5.

(* Ale : *)
Definition wrong_tail {A} l : {{l0 | exists x:A, x::l0 = l}} := !!.

Eval compute in wrong_tail [2;3;4].

Close Scope option_scope.
  
(* hybrydowa suma rozlaczna : zawiera czesc "konstruktywna" i "logiczna" *)
Print sumor.

Extraction sumor.

Notation "[[ x ]]" := (inleft _ (ret x)).
Notation "!!" := (inright _ _).

Check [[ [2;3] ]].

Definition tail_partial {A} (l:list A) : 
{l' : list A | exists x, cons x l' = l} + {l = []}.
refine (match l with
| [] => !!
| h::t => [[ t ]]
end); eauto.
Defined.

Eval compute in tail_partial [4;5].
Eval compute in @tail_partial nat [].

Extraction tail_partial.
Extraction sumor.

(**)

Section Remove.

Variable A : Type.
Hypothesis eq_A_dec : forall (x y:A), {x = y} + {x <> y}.

Notation " x == y " := (eq_A_dec x y) (at level 90) : type_scope.

Fixpoint remove (x:A) (l:list A) : list A :=
match l with
| [] => []
| h::t => if h == x then remove x t else h::remove x t
end.

Definition remove2 (x:A) (l:list A) : list A:=
let f := fix rem x l {struct l} :=
match l with
| [] => []
| h::t => if h == x then rem x t else h::rem x t
end in f x l.

Lemma isnil_dec (l:list A) : {l = []} + {l <> nil}.
Proof.
decide equality.
Defined.

(* a co z taka specyfikacja: *)

Fixpoint remove3 (x:A) (l: list A) : l <> [] -> list A :=
(*
match l return l <> [] -> list A with
| [] => fun p => nil_not_nil_F _ p
| h::t => fun p => if h == x then remove3 x t _ else h::remove3 x t _
end.
*)
match l with
| [] => fun p => nil_not_nil_F _ p
| h::t => match isnil_dec t with
          | left _ => fun _ => if h == x then [] else [h]
          | right H => fun _ => if h == x then remove3 x t H 
                                else h :: remove3 x t H
          end
end.

Definition remove4 : forall (x:A) (l: list A), l <> [] -> list A.
refine (
fix rem x l : l <> [] -> list A := 
match l with
| [] => fun p => !
| h::t => 
  match isnil_dec t with
    | left _ => fun _ => if h == x then [] else [h]
    | right H => fun _ => if h == x then rem x t H else h :: rem x t H
  end
end); eauto.
Defined.

Check List.remove.

Definition P : A -> list A -> list A -> Prop := 
fun x l' l => l' = List.remove eq_A_dec x l.

Hint Unfold P.
Print HintDb core.

Notation " # t " := (proj1_sig t) (at level 60) : spec_scope.

Definition remove_spec : forall (x:A) (l:list A),
   { l':list A | P x l' l}.
refine (
fix rem (x:A) (l:list A) : { l':list A | P x l' l} := 
match l with
| [] => ret []
| h::t => if h == x then ret #(rem x t) else ret (h :: #(rem x t))
end); auto;
elim rem; intros; subst; unfold P in *; simpl;
match goal with
| [ |- context [eq_A_dec ?x ?y] ] => elim (eq_A_dec x y); intros; subst; auto
end. 
Defined.

End Remove.

Check remove_spec.
Extraction remove_spec.


Require Import Peano_dec.

Eval compute in remove_spec _ eq_nat_dec 3 [1;2;3;4;3].

Print sig.
Print sigT.
Print sig2.
Locate "{ _ : _ & _ }".
Print Scope type_scope.

Notation " [ x , y ] " := (existT _ x (exist _ y _)) : spec_scope.

Definition tail_specT : forall A (l : list A), l <> nil -> 
{ l' : list A  & { x : A | cons x l' = l} }.
refine (fun A l =>
match l with
| nil => fun p => !
| h::t => fun _ => [t, h]
end); eauto.
Defined.

Extraction tail_specT.
Extraction sigT.

Close Scope spec_scope.

(* typechecking *)

Inductive exp : Set :=
| num : nat -> exp
| add : exp -> exp -> exp
| bval : bool -> exp
| and : exp -> exp -> exp
| isz : exp -> exp.

Notation " # n " := (num n) (at level 60, no associativity) : exp_scope.
Notation " a1 + a2 " := (add a1 a2) (at level 50, left associativity) : exp_scope.
Notation " b1 & b2 " := (and b1 b2) (at level 40, left associativity) : exp_scope.
Notation " 0 ? a " := (isz a) (at level 37, no associativity) : exp_scope.
Notation "[ x ; .. ; y ]" := (add x .. (add y (num 0)) ..) : exp_scope.

Open Scope exp_scope.

Inductive tp := Nat | Bool.

Reserved Notation " |- e ::: T " (at level 70).

Inductive typing_j : exp -> tp -> Prop :=
| t_num : forall n:nat, 
          |- #n ::: Nat
| t_add : forall a1 a2, 
          |- a1 ::: Nat-> |- a2 ::: Nat-> |- a1 + a2 ::: Nat
| t_bval : forall b, 
           |- bval b ::: Bool
| t_and : forall b1 b2, 
          |- b1 ::: Bool-> |- b2 ::: Bool-> |- b1 & b2 ::: Bool
| t_isz : forall a, 
          |- a ::: Nat-> |- 0? a ::: Bool
where " |- e ::: T " := (typing_j e T).

Hint Constructors typing_j.

Ltac solve_by_inversion :=
match goal with
| [ H : |- _ ::: _ |- _ ] => solve [inversion H; subst; auto]
| _ => idtac
end.

Ltac destruct_all :=
repeat match goal with
| [ H : { T : _ | |- ?e ::: T  } |- _ ] => destruct H
| [ H :  _ + { _ } |- _ ] => destruct H
| [ H : tp |- _ ] =>
  match goal with
  | [ H0 : |- ?e ::: H |- _ ] => destruct H
  | _ => idtac 
  end
| _ => idtac
end.

Ltac do_inversions n :=
match n with
| O => idtac
| S ?m => match goal with
         | [ H : |- _ ::: _ |- _ ] => inversion H; subst; clear H; do_inversions m
         | _ => idtac
         end
end.

Lemma typing_det :
forall e T1 T2,
|- e ::: T1 -> |- e ::: T2 -> T1 = T2.
Proof.
induction 1; intros; solve_by_inversion.
Qed.

Hint Resolve typing_det.
 
(* do uzupelnienia - cwiczenie na pozniej *)
Ltac magic_wand := idtac.

Lemma typing_dec :
forall e:exp, { T:tp | |- e ::: T} + {forall T:tp, ~ |- e ::: T}.
Proof.
induction e; intros; destruct_all; magic_wand.
Admitted.

Check typing_dec.
Extraction typing_dec.

(* notacja monadyczna *)
Notation " T <-- e1 ; e2 " := (match e1 with
                                       | inleft (exist _ T _) => e2
                                       | inright _ => _
                                       end) (right associativity, at level 60).

Notation " [[ x ]] " := (inleft _ (exist _ x _)).
Notation " e1 ~> e2 " := (if e1 then e2 else inright _ _) (at level 55).   

Lemma eq_tp_dec :
forall T1 T2:tp, {T1 = T2} + {T1 <> T2}.
Proof.
decide equality.
Defined.

Ltac magic_wand' :=
match goal with
| [ |- |-  _ ::: _ ] => solve [subst; constructor; eauto]
| [ |- forall _ , ~ |- _ ::: _ ] => solve [intros; intro; do_inversions 1; eauto]
| [ H : forall _, ~ |- _ ::: _ |- _ + { _ } ] => 
solve [subst; right; intros; intro; do_inversions 1; eelim H; eauto]
| _ => idtac
end.

Definition typing_dec' :
forall e:exp, { T:tp | |- e ::: T} + {forall T:tp, ~ |- e ::: T}.
refine 
(fix typ (e:exp) : { T:tp | |- e ::: T} + {forall T:tp, ~ |- e ::: T} :=
match e with
| #n => [[Nat]]
| a1 + a2 => 
T1 <-- typ a1; 
T2 <-- typ a2; 
eq_tp_dec T1 Nat ~> (eq_tp_dec T2 Nat ~> [[Nat]])
| bval b => [[Bool]]
| b1 & b2 =>
T1 <-- typ b1;
T2 <-- typ b2;
eq_tp_dec T1 Bool ~> (eq_tp_dec T2 Bool~> [[Bool]])
| 0? a => 
T1 <-- typ a; 
eq_tp_dec T1 Nat ~> [[Bool]]
end);
magic_wand'.
Defined.

Extraction typing_dec'.

Eval compute in typing_dec' (add (num 3) (num 4)).
Eval compute in typing_dec' (add (num 3) (bval true)).

Definition interpret_tp (t:tp) : Set :=
match t with
| Bool => bool
| Nat => nat
end.


Definition eval (e:exp) {T} (H : |- e ::: T) : interpret_tp T.
(*
induction H.
*)
generalize T H; clear T H.
induction e; intros.
assert (T=Nat) by (inversion H; auto); rewrite H0; simpl.
exact n.
assert (T=Nat) by (inversion H; auto); rewrite H0; simpl.
assert (|- e1 ::: Nat) by (inversion H; auto).
assert (|- e2 ::: Nat) by (inversion H; auto).
exact (Nat.add (IHe1 Nat H1) (IHe2 Nat H2)).
assert (T= Bool) by (inversion H; auto); rewrite H0; simpl.
exact b.
assert (T=Bool) by (inversion H; auto); rewrite H0; simpl.
assert (|- e1 ::: Bool) by (inversion H; auto).
assert (|- e2 ::: Bool) by (inversion H; auto).
exact (andb (IHe1 _ H1) (IHe2 _ H2)).
assert (T=Bool) by (inversion H; auto); rewrite H0; simpl.
assert (|- e ::: Nat) by (inversion H; auto).
exact (if eq_nat_dec (IHe _ H1) 0 then true else false).
Defined.

Print eval.
Extraction Language Haskell.
Extraction eval.
Extraction interpret_tp.


Inductive llist {A:Set} : nat -> Set :=
| lnil : llist 0
| lcons : forall n, A -> llist n -> llist (S n).

(*
Definition nth {A n} (l : @llist A n) m : m < n -> A.
*)

Inductive fin : nat -> Set :=
| fst : forall n, fin (S n)
| next : forall n, fin n -> fin (S n).

Check fst 2.
Check next _ (fst 1).
Check next _ (next _ (fst 0)).

(*
Fixpoint get {A n} (l : @llist A n) {struct l} : fin n -> A :=
match l with                  
| lcons _ x l' => fun index => 
                  match index in fin (S n) return A with
                  | fst _ => x
                  | next _ index' => get l' index'
                  end
| lnil => fun index => 
          match index in fin n return match n with 0 => A | _ => unit end with
          | fst _ => tt
          | next _ _ => tt
          end
end.
*)

(*
Fixpoint get {A n} (l : @llist A n) {struct l} : fin n -> A :=
match l (*in llist n return fin n -> A*) with                  
| lcons _ x l' => fun index => 
                  match index in fin (S n) return llist n -> A with
                  | fst _ => fun _ => x
                  | next _ index' => fun l1 => get l1 index'
                  end l'
| lnil => fun index => 
          match index in fin n return match n with 0 => A | _ => unit end with
          | fst _ => tt
          | next _ _ => tt
          end
end.
*)

Fixpoint get {A n} (l : @llist A n) {struct l} : fin n -> A :=
match l (*in llist n return fin n -> A*) with                  
| lcons _ x l' => fun index => 
                  match index in fin (S n) return (fin n -> A) -> A with
                  | fst _ => fun _ => x
                  | next _ index' => fun f => f index'
                  end (get l')
| lnil => fun index => 
          match index in fin n return match n with 0 => A | _ => unit end with
          | fst _ => tt
          | next _ _ => tt
          end
end.





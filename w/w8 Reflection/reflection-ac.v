(* reflection-ac.v *)
(* Na podstawie przykladu z Coq'Art *)

(*** Associativity ***)

Inductive bin : Set := 
| node : bin -> bin -> bin
| leaf : nat -> bin.

Fixpoint flatten_aux (t fin : bin){struct t} : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
  | x => node x fin
  end.

Fixpoint flatten (t : bin) : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten t2)
  | x => x
  end.

Require Import List.

Fixpoint bin_nat (t : bin) (l : list nat) {struct t} : nat :=
  match t with
  | node t1 t2 => bin_nat t1 l + bin_nat t2 l
  | leaf n => nth n l 0
  end.

Theorem flatten_aux_valid : forall (t t' : bin) (l : list nat), 
  bin_nat t l + bin_nat t' l = bin_nat (flatten_aux t t') l.
Admitted.

Theorem flatten_valid : forall (t : bin) (l : list nat), 
  bin_nat t l = bin_nat (flatten t) l.
Admitted.

Theorem flatten_valid_2 : forall (t t' : bin) (l : list nat), 
  bin_nat (flatten t) l = bin_nat (flatten t') l -> bin_nat t l = bin_nat t' l.
Proof.
intros t1 t2 l H.
rewrite (flatten_valid t1).
rewrite (flatten_valid t2).
assumption.
Qed.

Ltac term_list l v :=
  match v with
  | (?X1 + ?X2) => let l2 := term_list l X2 
                               in term_list l2 X1
  | ?X => constr : (cons X l) 
  end.

Ltac compute_rank l n v :=
  match l with
  | (cons ?X1 ?X2) => let tl := constr:(X2)
                                    in match constr: (X1 = v) with
                                        | (?X = ?X) => n
                                        | _ => compute_rank tl (S n) v
                                        end
  end.

Ltac find l n v :=
match l with
| nil => -1
| cons v ?L => n
| cons ?X ?L => find L (S n) v 
end.

Goal True.
let n:=find (@nil nat) 0 (3*4) in idtac n.
let n:=find constr:((cons 12 nil)) 0 (3*4) in idtac n.
let n:=find constr:((cons 1 (cons 12 nil))) 0 12 in idtac n.

Ltac model_aux l v :=
  match v with
  | (?X1 + ?X2) => let r1 := model_aux l X1 with r2 := model_aux l X2 
                               in constr : (node r1 r2)
  | ?X => let n := compute_rank l 0 X
                in constr : (leaf n)
  end. 

Ltac model v :=
  let l := term_list (nil (A := nat)) v
  in let t := model_aux l v
      in constr : (bin_nat t l).

Ltac assoc_eq_nat :=
  match goal with
  | [ |- (?X1 = ?X2 : nat) ] =>
      let term1 := model X1 with term2 := model X2
      in (change (term1 = term2); apply flatten_valid_2; reflexivity)
  end.

Theorem reflection_test'' : forall x y z t u : nat, 
  x+(1+y+z+(t+u)) = x+1+y+(z+(t+u)). 
(*  (x+1)+y = x+(1+y).*)
Proof.
intros.
let term1 := model (x+(1+y+z+(t+u))) with term2 := model (x+1+y+(z+(t+u)))
      in (change (term1 = term2)).
apply flatten_valid_2.
simpl (flatten _).
reflexivity.
(*assoc_eq_nat.*)
Qed.

Print reflection_test''.

(*** Commutativity ***)

Require Import PeanoNat.

Print Nat.leb.
Locate "<=?".

Fixpoint insert_bin (n : nat) (t : bin) {struct t} : bin :=
  match t with
  | leaf m => if n <=? m 
              then node (leaf n) (leaf m)
              else node (leaf m) (leaf n)                      
  | node (leaf m) t' => if n <=? m 
                        then node (leaf n) t
                        else node (leaf m) (insert_bin n t')
  | t => node (leaf n) t
  end.

Fixpoint sort_bin (t : bin) : bin :=
  match t with
  | node (leaf n) t' => insert_bin n (sort_bin t')
  | t => t
  end.

Theorem insert_is_plus : forall (l : list nat) (n : nat) (t : bin),
  bin_nat (insert_bin n t) l = (nth n l 0) + (bin_nat t l).
Admitted.

Theorem sort_eq : forall (l : list nat) (t : bin),
  bin_nat (sort_bin t) l = bin_nat t l.
Admitted.

Theorem sort_eq_2 : forall (l : list nat) (t1 t2 : bin),
  bin_nat (sort_bin t1) l = bin_nat (sort_bin t2) l ->
  bin_nat t1 l = bin_nat t2 l.
Admitted.

Ltac comm_eq :=
  match goal with
  | [ |- (?X1 = ?X2 :> nat) ] => 
    let l := term_list (nil (A:=nat)) X1
    in let term1 := model_aux l X1
        with term2 := model_aux l X2
        in (change (bin_nat term1 l = bin_nat term2 l);
             apply flatten_valid_2;
             apply sort_eq_2;
             reflexivity)
  end.

Theorem reflection_test4 : forall x y z : nat, x+(y+z) = (z+x)+y.
Proof.
intros x y z.
(*comm_eq. *)
let l := term_list (nil (A:=nat)) (x+(y+z))
    in let term1 := model_aux l (x+(y+z))
        with term2 := model_aux l ((z+x)+y)
        in (change (bin_nat term1 l = bin_nat term2 l)).
apply flatten_valid_2.
apply sort_eq_2.
simpl (sort_bin _).
reflexivity.
Qed.


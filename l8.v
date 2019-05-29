(** * Lista zadań nr 8 *)
(** autorstwa Wojciecha Kołowskiego *)
(** zadania punktowane za 0p nie będą sprawdzane *)

(** **** Zadanie 1 - 4p *)

(*
    Zdefiniuj typ potencjalnie nieskończonych drzew binarnych trzymających
    wartości typu A w węzłach, jego relację bipodobieństwa, predykaty
    "skończony" i "nieskończony" oraz funkcję mirror, która zwraca
    lustrzane odbicie drzewa. Udowodnij, że bipodobieństwo jest relacją
    równoważności i że funkcja mirror jest inwolucją (tzn. mirror (mirror t)
    jest bipodobne do t), która zachowuje właściwości bycia drzewem
    skończonym/nieskończonym. Pokaż, że drzewo nie może być jednocześnie
    skończone i nieskończone.
*)

CoInductive LTree (A : Type) : Type :=
{
  unnode : option (LTree A * A * LTree A);
}.

Definition LL {A : Type} (t : LTree A) := 
  match t with
  | {| unnode := a |} => {| unnode := a |}
  end.

Lemma LLid : forall (A : Type) (t : LTree A), t = LL t.
Proof.
  intros. unfold LL. destruct t. reflexivity.
  Qed.

Lemma ltree : forall (A : Type) (t : LTree A), exists r, t = {| unnode := r |}.
Proof.
  intros.
  case t as [ t' ]. induction t'; eexists; eauto.
  Qed.

CoInductive bisym {A : Type} (t1 t2 : LTree A) : Prop :=
| bileaf : unnode A t1 = None /\ unnode A t2 = None -> bisym t1 t2
| binode : forall t1l v1 t1r t2l v2 t2r,
    unnode A t1 = Some (t1l, v1, t1r) ->
    unnode A t2 = Some (t2l, v2, t2r) ->
    v1 = v2 ->
    bisym t1l t2l ->
    bisym t1r t2r -> 
    bisym t1 t2
.

Definition leaf {A : Type} : LTree A := {| unnode := None |}.

Definition node {A : Type} l v r : LTree A := {| unnode := Some (l, v, r) |}.

Inductive Finite {A : Type} (t : LTree A) : Prop :=
| finleaf : unnode A t = None -> Finite t
| finnode : forall l v r, unnode A t = Some (l,v,r) -> Finite l -> Finite r -> Finite t
.

CoInductive Infinite {A : Type} (t : LTree A) : Prop :=
{
  v : A;
  l : LTree A;
  r : LTree A;
  p : unnode A t = Some (l, v, r);
  infl : Infinite A l;
  infr : Infinite A r;
}.

Print Infinite.

CoFixpoint mirror {A : Type} (t : LTree A) : LTree A := 
  match unnode A t with
  | None => leaf
  | Some (l, v, r) => node (mirror r) v (mirror l)
  end
.

Ltac d3 tup l v r := 
  let p := fresh "p" in destruct tup as [p r]; destruct p as [l v].
Ltac tryinv := 
  match goal with
  | [ H : _ |- _ ] => solve [inversion H; auto]
  | _ => idtac
  end.

Lemma bisym_refl : forall (A : Type) (t : LTree A), bisym t t.
Proof.
  cofix CH. intros.
  remember (unnode A t) as o eqn:H. induction o as [ tup | ].
  - d3 tup l v r. eapply binode; eauto.
  - apply bileaf; auto.
  Qed.

Lemma bisym_sym : forall (A : Type) (t1 t2 : LTree A), bisym t1 t2 -> bisym t2 t1.
Proof.
  cofix CH. intros. inversion H.
  - apply bileaf. destruct H0. split; auto.
  - eapply binode; eauto.
  Qed.

Lemma bisym_trans : forall (A : Type) (t1 t2 t3 : LTree A),
  bisym t1 t2 -> bisym t2 t3 -> bisym t1 t3.
Proof.
  cofix CH. intros. inversion H; inversion H0.
  - eapply bileaf. destruct H1. destruct H2. split; auto.
  - destruct H1. destruct (unnode A t2); tryinv.
  - destruct H6. destruct (unnode A t2); tryinv.
  - rewrite H2 in H6. inversion H6. subst.
    eapply binode; eauto.
  Qed.

Lemma pack_unnode : forall A t res, 
  res = unnode A t ->
  t = {| unnode := res |}.
Proof.
  intros. case (ltree A t). intros. rewrite H0 in H. cbn in H.
  rewrite H. assumption. 
Qed.

Lemma mirror_involution : forall (A : Type) (t : LTree A), bisym (mirror (mirror t)) t.
Proof.
  cofix CH. intros.
  remember (unnode A t) as o eqn:H. induction o as [ tup | ].
  - d3 tup l v r.
    eapply binode; eauto.
    rewrite (pack_unnode A t (Some (l,v,r))).
    cbn. auto. auto.
  - eapply bileaf. split; auto.
    erewrite (pack_unnode A t); eauto.
    cbn. reflexivity.    
  Qed.

Lemma mirror_finite : forall (A : Type) (t : LTree A),
  Finite t -> Finite (mirror t).
Proof.
  intros.
  induction H; case (ltree A t) as [ m ].
  - apply finleaf. cbn. rewrite H0 in H. cbn in *. subst. cbn. reflexivity.
  - apply finnode with (l0 := mirror r) (v0 := v) (r0 := mirror l); eauto.
    subst. cbn in *. subst. cbn. reflexivity.
  Qed.

Lemma mirror_infinite : forall (A : Type) (t : LTree A),
  Infinite t -> Infinite (mirror t).
Proof.
  cofix CH. intros. inversion H.
  case (ltree A t) as [ m ]. induction m; 
    rewrite H0 in p; cbn in p; inversion p; subst.
  apply Build_Infinite with (v := v) (l := mirror r) (r := mirror l); auto.
  Qed.

Lemma not_both : forall (A : Type) (t t' : LTree A), ~ (Finite t /\ Infinite t).
Proof.
  intros. intro H. destruct H as [ Hf Hi ].
  induction Hf; case (ltree A t) as [ m ].
  - inversion Hi. subst. cbn in *. subst. inversion p.
  - inversion Hi. subst. cbn in *. subst. inversion p. subst. auto.
  Qed.

(** **** Zadanie 2 - 4p *)
(*

    Znajdź taką rodzinę typów koinduktywnych C, że dla dowolnego
    typu A, C A jest w bijekcji z typem funkcji nat -> A. Przez
    bijekcję będziemy tu rozumieć funkcję, która ma odwrotność, z którą
    w obie strony składa się do identyczności.

    Uwaga: nie da się tego udowodnić bez użycia dodatkowych aksjomatów,
    które na szczęście są bardzo oczywiste i same się narzucają.

*)

CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.
Arguments hd {A}.
Arguments tl {A}.

CoInductive stream_eq {A : Type} (s1 s2 : Stream A) : Prop :=
{
    hds : hd s1 = hd s2;
    tls : stream_eq A (tl s1) (tl s2);
}.

Lemma stream_eq_refl :
  forall (A : Type) (s : Stream A), stream_eq s s.
Proof.
  cofix CH. constructor; auto.
Qed.

Lemma stream_eq_sym :
  forall (A : Type) (s1 s2 : Stream A),
    stream_eq s1 s2 -> stream_eq s2 s1.
Proof.
  cofix CH.
  destruct 1 as [hds tls]. constructor; auto.
Qed.

Lemma stream_eq_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    stream_eq s1 s2 -> stream_eq s2 s3 -> stream_eq s1 s3.
Proof.
  cofix CH.
  destruct 1 as [hds1 tls1], 1 as [hds2 tls2].
  constructor; eauto. rewrite hds1. assumption.
Qed.

Fixpoint nth {A : Type} (s : Stream A) (n : nat) :=
  match n with
  | O => s
  | S m => nth (tl s) m
  end
.

Definition stream_to_seq {A : Type} (s : Stream A) : nat -> A :=
  fun n => hd (nth s n).

CoFixpoint seq_to_stream {A : Type} (f : nat -> A) : Stream A :=
  {|
    hd := f 0;
    tl := seq_to_stream (fun n => f (S n))
  |}
.

Lemma stream_id : forall (A : Type) (s : Stream A),
  stream_eq s (seq_to_stream (stream_to_seq s)).
Proof.
  cofix CH. intros.
  constructor.
    cbn; unfold stream_to_seq; cbn; reflexivity.
    cbn. constructor.
      cbn; unfold stream_to_seq; cbn; reflexivity.
      apply CH.
Qed.

Require Import FunctionalExtensionality.

Lemma seq_id : forall (A : Type) (f : nat -> A),
  f = (stream_to_seq (seq_to_stream f)).
Proof.
  intros.
  apply functional_extensionality_dep. intro.
  generalize dependent f.
  induction x; intros.
  - cbn. reflexivity.
  - apply IHx with (f := fun n => f (S n)).
  Qed.

(** **** Zadanie 3 - 0p *)

(*

    Sprawdź, czy dobrze ufundowana jest następująca relacja porządku
    (mam nadzieję, że obrazek jest zrozumiały):
    0 < 1 < ... < ω < ω + 1 < ... < 2 * ω

     Oczywiście najpierw musisz wymyślić, w jaki sposób zdefiniować taką
     relację.

*)

(** **** Zadanie 4 - 4p *)

(*

    Niech (B, R) będzie typem wyposażonym w relację dobrze ufundowaną R.
    Zdefiniuj po współrzędnych relację porządku na funkcjach A -> B
    i rozstrzygnij, czy relacja ta jest dobrze ufundowana.

    Uwaga: zadanie jest trochę podchwytliwe.

*)

(** **** Zadanie 5 - 0p *)

(*

    Zdefiniuj pojęcie "nieskończonego łańcucha malejącego" (oczywiście
    za pomocą koindukcji) i udowodnij, że jeżeli relacja jest dobrze
    ufundowana, to nie ma nieskończonych łańcuchów malejących.

*)


(** **** Zadanie 6 - 0p *)

(*

    Zdefiniuj na listach porządek według długości i pokaż, że jest on
    dobrze ufundowany.

    Zdefiniuj przez rekursję dobrze ufundowaną funkcję rotn, która
    bierze liczbę n oraz listę i zwraca listę, w której bloki o
    długości dokładnie [n + 1] zostały odwrócone, np.
    rotn 0 [1; 2; 3; 4; 5; 6; 7] = [1; 2; 3; 4; 5; 6; 7]
    rotn 1 [1; 2; 3; 4; 5; 6; 7] = [2; 1; 4; 3; 6; 5; 7]
    rotn 2 [1; 2; 3; 4; 5; 6; 7] = [3; 2; 1; 6; 5; 4; 7]

    Wskazówka: zdefiniuj funkcją pomocniczą split, która dzieli listę
    na blok odpowiedniej długości i resztę listy.

    Następnie przyjmij, że funkcja rotn spełnia swoje równanie
    rekurencyjne (bonus, bardzo trudne: udowodnij, że faktycznie
    tak jest).

    Zdefiniuj relację opisującą wykres funkcji rotn. Pokaż, że
    definicja wykresu jest poprawna i pełna oraz wyprowadź z niej
    regułę indukcji funkcyjnej. Użyj jej, żeby udowodnić, że funkcja
    rotn jest inwolucją dla dowolnego n, tzn. rotn n (rotn n l) = l.

*)

(** **** Zadanie 7 - 7p *)

(*

    Zdefiniuj funkcję rotn (i wszystkie funkcje pomocnicze) jeszcze raz,
    tym razem za pomocą komendy Function. Porównaj swoje definicje wykresu
    oraz reguły indukcji z tymi automatycznie wygenerowanymi. Użyj taktyki
    functional induction, żeby jeszcze raz udowodnić, że rotn jest
    inwolucją (i wszystkie lematy też). Policz, ile pisania udało ci się
    dzięki temu zaoszczędzić.

    Czy w twoim rozwiązaniu są lematy, w których użycie indukcji funkcyjnej
    znacznie utrudnia przeprowadzenie dowodu? W moim jest jeden taki.

*)

(** **** Zadanie 8 - 0p *)

(*

    Zainstaluj plugin Equations:
    https://github.com/mattam82/Coq-Equations

    Przeczytaj tutorial:
    https://raw.githubusercontent.com/mattam82/Coq-Equations/master/doc/equations_intro.v

    Następnie znajdź jakiś swój dowód przez indukcję, który był skomplikowany
    i napisz prostszy dowód z potem za pomocą komendy [Equations] i taktyki
    [funelim].

    Dobrze byłoby, gdyby nie była to kolejna przeróbka poprzedniego zadania.

*)

(** **** Zadanie bonusowe - 10p *)

(*

    Nie ma to wprawdzie żadnego związku z tematem wykładu, ale miło by było
    pamiętać, że Coq to nie jest jakiś tam biedajęzyk programowania, tylko
    pełnoprawny system podstaw matematyki (no, prawie...). W związku z tym
    bonusowe zadanie:

    Pokaż, że nat <> Type.

*)
(*
  In emacs use
     (setq coq-compile-before-require t)
     (setq coq-load-path-include-current t)
  in init file.
*)

Require Import objoidAndMapoid.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Section pushout.

(* We specify what we want a pushout to be. *)

Structure Pushout (A B C:objoid) (f:mapoid A B) (g:mapoid A C):Type := {
    object:objoid;
    i0:mapoid B object;
    i1:mapoid C object;
    univ_exist (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a1:A, a1 |> f |> h = a1 |> g|> k):
        (exists z:mapoid object Z, forall b:B, forall c:C,
            ( b |> i0 |> z = b|>h) /\ ( c|>i1|> z = c|>k));
    univ_unique (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a1:A, a1 |> f |> h = a1 |> g|> k):
    (forall y z:mapoid object Z, (
            (forall b:B, b|>i0|>z = b|>h) /\
            (forall c:C, c|>i1|>z = c|>k) /\
            (forall b:B, b|>i0|>y = b|>h) /\
            (forall c:C, c|>i1|>y = c|>k)) 
                -> forall d:object, d|>z = d|>y)
}.

(* We define a function that constructs the pushout. *)

(*  First we define the pushout object.
    Remember this is before asserting the equivalence relation. *)
Inductive DisjointUnion (B C:objoid):Type :=
| b: carrier B -> DisjointUnion B C
| c: carrier C -> DisjointUnion B C.

Arguments b {B} {C}.
Arguments c {B} {C}.

(* Now we define the equivalence relation on the pushout object. *)
Inductive PushoutEq (A B C:objoid) (f:mapoid A B) (g:mapoid A C): relation (DisjointUnion B C) :=
| beq (b1 b2:carrier B) (H:b1=b2):  PushoutEq A B C f g (b b1) (b b2)
| ceq (c1 c2:carrier C) (H:c1=c2): PushoutEq A B C f g (c c1) (c c2).

Arguments PushoutEq {A}{B}{C}.

(* And then combine this with the disjoint union to get an objoid. *)
Definition PushoutObjoid (A B C:objoid) (f:mapoid A B) (g:mapoid A C):objoid :=
  gen_obj (PushoutEq f g).

Arguments PushoutObjoid {A}{B}{C}.

(*  The following is a little awkward.
    We seem to need three different maps for essentially the same thing:
        1. the inductive generator b;
        2. the function ib;
        3. the mapoid mapoid_b *)

Definition ib (A B C:objoid) (f:mapoid A B) (g:mapoid A C):
    carrier B -> carrier (PushoutObjoid f g) :=
        b.

Lemma b_pres (A B C:objoid) (f:mapoid A B) (g:mapoid A C):
    forall a1 a2 : B, a1 = a2 -> ib A B C f g a1 = ib A B C f g a2.
Proof.
    intros.
    rewrite H.
    apply eq_refl.
Qed.

Definition mapoid_b (A B C:objoid) (f:mapoid A B) (g:mapoid A C):mapoid B (PushoutObjoid f g) := {|
map:= ib A B C f g;
pres:= b_pres A B C f g
|}.

Arguments mapoid_b {A}{B}{C}.

(*  Two awkward manual 'tactics'.
    I can't figure out how to do the proof in uniqueness_univ without them.
    Might well be because of the inefficient definitions above.
    (But does work though...) *)

Lemma mapoid_b_unfold (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (b1:B) (Z:objoid) (z:mapoid (PushoutObjoid f g) Z):
    b1|>mapoid_b f g|> z = ib A B C f g b1 |>z.
Proof.
    apply pres.
    apply mapoid_b.
    apply eq_refl.
Qed.

Lemma elementwise_b (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (b1:B):
    ib A B C f g b1 = b b1.
Proof.
    auto.
Qed.

Definition ic (A B C:objoid) (f:mapoid A B) (g:mapoid A C): carrier C -> carrier (PushoutObjoid f g) := c.

Lemma c_pres (A B C:objoid) (f:mapoid A B) (g:mapoid A C):
    forall a1 a2 : C, a1 = a2 -> ic A B C f g a1 = ic A B C f g a2.
Proof.
    intros.
    rewrite H.
    apply eq_refl.
Qed.

Definition mapoid_c (A B C:objoid) (f:mapoid A B) (g:mapoid A C):mapoid C (PushoutObjoid f g) := {|
map:= ic A B C f g;
pres:= c_pres A B C f g
|}.

Arguments mapoid_c {A}{B}{C}.

Lemma mapoid_c_unfold (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (c1:C) (Z:objoid) (z:mapoid (PushoutObjoid f g) Z):
    c1|>mapoid_c f g|> z = ic A B C f g c1 |>z.
Proof.
    apply pres.
    apply mapoid_c.
    apply eq_refl.
Qed.

Lemma elementwise_c (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (c1:C):
    ic A B C f g c1 = c c1.
Proof.
    auto.
Qed.

(*  We define the factorisation and then prove the universal property of the pushout. *)

Definition factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k) (d1:carrier (PushoutObjoid f g)):
    carrier Z :=
    match d1 with
    | b b1 => b1 |> h
    | c c1 => c1 |> k
    end.

Lemma pres_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k) (d1 d2:(carrier (PushoutObjoid f g))) (H2:d1=d2):
    factorisation A B C f g Z h k H d1 = factorisation A B C f g Z h k H d2.
Proof.
    rewrite H2.
    apply eq_refl.
Qed.   

Definition mapoid_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k):
    mapoid (PushoutObjoid f g) Z := {|
    map:=factorisation A B C f g Z h k H;
    pres:=pres_factorisation A B C f g Z h k H
    |}.

Arguments mapoid_factorisation {A}{B}{C}.

(* Lemma mapoid_b_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k):
    (forall b:B, b |> mapoid_b f g |> mapoid_factorisation f g Z h k H = b|>h).
Proof.
    intro.
    simpl.
    apply eq_refl.
Qed.

Lemma mapoid_c_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k):
    (forall c:C, c|> mapoid_c f g |> mapoid_factorisation f g Z h k H = c|>k).
Proof.
intro.
simpl.
apply eq_refl.
Qed. *)
(* 
Arguments mapoid_b_factorisation {A}{B}{C}.
Arguments mapoid_c_factorisation {A}{B}{C}. *)

Lemma existence_univ (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid)
    (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k):
    (exists z:mapoid (PushoutObjoid f g) Z, forall b:B, forall c:C,
        ( b |> mapoid_b f g |> z = b|>h) /\ ( c|> mapoid_c f g|> z = c|>k)).
Proof.
    exists (mapoid_factorisation f g Z h k H).
    intros.
    split.
    simpl.
    apply eq_refl.

    simpl.
    apply eq_refl.
Qed.

Lemma uniqueness_univ (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid)
    (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k):
    (forall y z:mapoid (PushoutObjoid f g) Z, 
        ((forall b:B, b|>mapoid_b f g|>z = b|>h) /\
        (forall c:C, c|>mapoid_c f g|>z = c|>k)  /\
        (forall b:B, b|>mapoid_b f g|> y = b|>h) /\
        (forall c:C,c|>mapoid_c f g|> y = c|>k)) 
            -> forall d:(PushoutObjoid f g), d|>z = d|>y).
Proof.
    intros.
    elim d.
    simpl in H0.

    intro.
    destruct H0 as (H0&H1&H2&H3).
    specialize (H0 c0).
    specialize (H2 c0).
    rewrite (elementwise_b A B C f g) in H0.
    rewrite (elementwise_b A B C f g) in H2.
    rewrite H0.
    rewrite H2.
    apply eq_refl.

    intro.
    simpl in H0.
    destruct H0 as (H0&H1&H2&H3).
    specialize (H1 c0).
    specialize (H3 c0).
    rewrite (elementwise_c A B C f g) in H1.
    rewrite (elementwise_c A B C f g) in H3.
    rewrite H1.
    rewrite H3.
    apply eq_refl.
Qed.

(* The following function is the one we want to expose in the encapsulation. *)

Definition mk_pushout (A B C:objoid) (f:mapoid A B) (g:mapoid A C): Pushout A B C f g:= {|
        object := PushoutObjoid f g;
        i0 := mapoid_b f g;
        i1 := mapoid_c f g;
        univ_exist := existence_univ A B C f g;
        univ_unique := uniqueness_univ A B C f g
    |}.

End pushout.
Arguments mk_pushout {A}{B}{C}.
Arguments i1 {A}{B}{C}{f}{g}.
Arguments PushoutEq {A}{B}{C}.

Arguments mapoid_c {A}{B}{C}.


Section TestPushout.
  
Variables A B C D:objoid.
Variable f:mapoid A B.
Variable g:mapoid A C.
Variable H:
  forall a1 a2:A,
    a1|>f=a2|>f ->
    a1=a2.

Definition P := mk_pushout f g.

Proposition mapoid_c_mono:
  forall c1 c2:C,
    c1|>mapoid_c f g=c2|>mapoid_c f g ->
    c1=c2.
Proof.
  
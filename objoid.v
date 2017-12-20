Add LoadPath "/Users/mat/Documents/gitRepos/coq/".
Require Import objoidAndMapoid.


Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Section pushout.

Structure Pushout (A B C:objoid) (f:mapoid A B) (g:mapoid A C):Type := {
    object:objoid;
    i0:mapoid B object;
    i1:mapoid C object;
    univ_exist (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (a1:A) (H: a1 |> f |> h = a1 |> g|> k):
        (exists z:mapoid object Z, forall b:B, forall c:C,
            ( b |> i0 |> z = b|>h) /\ ( c|>i1|> z = c|>k));
    univ_unique (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (a1: A) (H: a1 |> f |> h = a1 |> g|> k):
    (forall y z:mapoid object Z, (
        forall b:B, forall c:C,
            ( b|>i0|>z = b|>h) /\
            ( c|>i1|>z = c|>k) /\
            (b|>i0|> y = b|>h) /\
            (c|>i1|> y = c|>k)) 
                -> forall d:object, d|>z = d|>y)
}.

(* We define the pushout object. *)

Inductive DisjointUnion (B C:objoid):Type :=
| b: carrier B -> DisjointUnion B C
| c: carrier C -> DisjointUnion B C.

Arguments b {B} {C}.
Arguments c {B} {C}.

Inductive PushoutEq (A B C:objoid) (f:mapoid A B) (g:mapoid A C): DisjointUnion B C -> DisjointUnion B C -> Prop :=
| beq (b1 b2:carrier B) (H:b1=b2):  PushoutEq A B C f g (b b1) (b b2)
| ceq (c1 c2:carrier C) (H:c1=c2): PushoutEq A B C f g (c c1) (c c2)
| aeq (a:carrier A): PushoutEq A B C f g (b (a|>f)) (c (a|>g))
| refl: forall d1:DisjointUnion B C, PushoutEq A B C f g d1 d1
| sym (d1 d2:DisjointUnion B C) (H:PushoutEq A B C f g d1 d2): PushoutEq A B C f g d2 d1
| trans (d1 d2 d3:DisjointUnion B C) (H1:PushoutEq A B C f g d1 d2) (H2:PushoutEq A B C f g d2 d3): PushoutEq A B C f g d1 d3.

Arguments PushoutEq {A}{B}{C}.
Arguments refl {A} {B} {C} {f} {g}.
Arguments sym {A} {B} {C} {f} {g}.
Arguments trans {A} {B} {C} {f} {g}.

Program Instance PushoutSetoid (A B C:objoid) (f:mapoid A B) (g:mapoid A C): Setoid (DisjointUnion B C) :=
{
    equiv:=PushoutEq f g;
    setoid_equiv:= {|
        Equivalence_Reflexive := refl;
        Equivalence_Symmetric := sym;
        Equivalence_Transitive :=trans
    |}
}.

Definition PushoutObject (A B C:objoid) (f:mapoid A B) (g:mapoid A C):objoid := {|
    carrier:= DisjointUnion B C;
    eq:= PushoutSetoid A B C f g
|}.

Arguments PushoutObject {A}{B}{C}.

(* We define the pushout inclusions. *)

Definition ib (A B C:objoid) (f:mapoid A B) (g:mapoid A C): carrier B -> carrier (PushoutObject f g) := b.

Lemma b_pres (A B C:objoid) (f:mapoid A B) (g:mapoid A C):
    forall a1 a2 : B, a1 = a2 -> ib A B C f g a1 = ib A B C f g a2.
Proof.
    intros.
    rewrite H.
    apply eq_refl.
Qed.

Definition mapoid_b (A B C:objoid) (f:mapoid A B) (g:mapoid A C):mapoid B (PushoutObject f g) := {|
map:= ib A B C f g;
pres:= b_pres A B C f g
|}.

Arguments mapoid_b {A}{B}{C}.

Lemma mapoid_b_unfold (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (b1:B) (Z:objoid) (z:mapoid (PushoutObject f g) Z):
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

Definition ic (A B C:objoid) (f:mapoid A B) (g:mapoid A C): carrier C -> carrier (PushoutObject f g) := c.

Lemma c_pres (A B C:objoid) (f:mapoid A B) (g:mapoid A C):
    forall a1 a2 : C, a1 = a2 -> ic A B C f g a1 = ic A B C f g a2.
Proof.
    intros.
    rewrite H.
    apply eq_refl.
Qed.

Definition mapoid_c (A B C:objoid) (f:mapoid A B) (g:mapoid A C):mapoid C (PushoutObject f g) := {|
map:= ic A B C f g;
pres:= c_pres A B C f g
|}.

Arguments mapoid_c {A}{B}{C}.

Lemma mapoid_c_unfold (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (c1:C) (Z:objoid) (z:mapoid (PushoutObject f g) Z):
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


(* We prove the universal property of the pushout. *)

Definition factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k) (d1:carrier (PushoutObject f g)):
    carrier Z :=
    match d1 with
    | b b1 => b1 |> h
    | c c1 => c1 |> k
    end.

Lemma pres_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k) (d1 d2:(carrier (PushoutObject f g))) (H2:d1=d2):
    factorisation A B C f g Z h k H d1 = factorisation A B C f g Z h k H d2.
Proof.
    rewrite H2.
    apply eq_refl.
Qed.
    

Definition mapoid_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k):
    mapoid (PushoutObject f g) Z := {|
    map:=factorisation A B C f g Z h k H;
    pres:=pres_factorisation A B C f g Z h k H
    |}.

Arguments mapoid_factorisation {A}{B}{C}.

Lemma mapoid_b_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k):
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
Qed.

Arguments mapoid_b_factorisation {A}{B}{C}.
Arguments mapoid_c_factorisation {A}{B}{C}.

Lemma existence_univ (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k):
    (exists z:mapoid (PushoutObject f g) Z, forall b:B, forall c:C,
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

Lemma trivia (x y:Type) (P Q:Prop):
    forall (x1:x) (y1:y), P/\Q -> (forall (x1:x) (y1:y), P)/\(forall (x1:x) (y1:y), Q).
Proof.
    intro.
    tauto.
Qed.

Lemma univ_pushout (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: forall a:A, a|>f|>h = a|>g|>k):
    (forall y z:mapoid (PushoutObject f g) Z, 
        ((forall b:B, b|>mapoid_b f g|>z = b|>h) /\ (forall c:C, c|>mapoid_c f g|>z = c|>k) /\ (forall b:B, b|>mapoid_b f g|> y = b|>h) /\ (forall c:C,c|>mapoid_c f g|> y = c|>k)) -> forall d:(PushoutObject f g), d|>z = d|>y).
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

End pushout.

Section pushout.

Variables A B C Z:objoid.
Variable f:mapoid A B.
Variable g:mapoid A C.

Inductive PushoutCarrier:Type :=
| c: carrier C -> PushoutCarrier
| b: carrier B -> PushoutCarrier.

Inductive PushoutEq:PushoutCarrier -> PushoutCarrier -> Prop :=
| beq (b1 b2:carrier B) (H:b1=b2):  PushoutEq (b b1) (b b2)
| ceq (c1 c2:carrier C) (H:c1=c2): PushoutEq (c c1) (c c2)
| aeq (a:carrier A): PushoutEq (b (a|>f)) (c (a|>g))
| refl: forall d1:PushoutCarrier, PushoutEq d1 d1
| sym (d1 d2:PushoutCarrier) (H:PushoutEq d1 d2): PushoutEq d2 d1
| trans (d1 d2 d3:PushoutCarrier) (H1:PushoutEq d1 d2) (H2:PushoutEq d2 d3): PushoutEq d1 d3.

Definition Pushout:objoid := {|
carrier:=PushoutCarrier;
eq:=PushoutEq;
eq_refl:= refl;
eq_sym:=sym;
eq_trans:=trans
|}.

Definition new_b: carrier B -> carrier Pushout := b.
Definition new_c: carrier C -> carrier Pushout := c.

Lemma pres_ib (b1 b2:carrier B) (H:b1=b2): new_b b1 = new_b b2.
Proof.
simpl.
apply beq.
assumption.
Qed.

Lemma pres_ic (c1 c2:carrier C) (H:c1=c2): new_c c1 = new_c c2.
Proof.
simpl.
apply ceq.
assumption.
Qed.

Definition ib: mapoid B Pushout := {|
map:=new_b;
pres:=pres_ib
|}.

Definition ic: mapoid C Pushout := {|
map:=new_c;
pres:=pres_ic
|}.

Variable h:mapoid B Z.
Variable k:mapoid C Z.

Variable H2:(f||>h) = (g||>k).

Definition carrier_out (d1:carrier Pushout): carrier Z :=
match d1 with
| b b1 => (b1 |> h)
| c c1 => (c1 |> k)
end.

Lemma pres_out (d1 d2:carrier Pushout) (H1:d1=d2): carrier_out d1 =carrier_out d2.
Proof.
elim H1.
intro.
intro.
intro.
simpl.
apply pres.
assumption.

intros.
simpl.
apply pres.
assumption.

intros.
simpl.
apply (eq_trans (mapoid_ext f h a)).
rewrite H2.
apply eq_sym.
apply (eq_trans (mapoid_ext g k a)).
apply eq_refl.

intros.
apply eq_refl.

intros.
apply eq_sym.
apply H0.

intro.
intro.
intro.
intro.
intro.
intro.
apply (eq_trans H).
Qed.

Definition mapoid_out := {|
map:=carrier_out;
pres:=pres_out
|}.

Lemma b_triangle (b1:carrier B): (new_b b1 |> mapoid_out) = (b1 |> h).
Proof.
simpl.
trivial.
Qed.

Lemma ib_triangle: (ib ||> mapoid_out) = h.
Proof.
elim ib.
intros.
elim mapoid_out.
intros.
elim h.
intros.
apply b_triangle.
    

Lemma factorisation_unique (H:(f||>h)=(g||>k)):
exists! z:mapoid Pushout Z,
( h = (ib ||> z)) /\ (k = (ic ||> z)).
Proof.
exists mapoid_out.
split.
split.
(* elim ib. *)
(* intros. *)
(* elim mapoid_out. *)
(* intros. *)


Structure PO := {
pushout:objoid;
i1:mapoid B pushout;
i2:mapoid C pushout;
factorisation (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H:(f||>h)=(g||>k)):
    exists! z:mapoid pushout Z,
    ( h = (i1 ||> z)) /\ (k = (i2 ||> z))
}.

Definition Pushout1 := {|
pushout:=Pushout;
i1:=ib;
i2:=ic;
factorisation:=mapoid_out
|}.

End pushout.

Arguments Pushout {A} {B} {C}.

Section Test.

Variables A B C:objoid.
Variable f:mapoid A B.
Variable g:mapoid A C.

Definition D:objoid := Pushout f g.

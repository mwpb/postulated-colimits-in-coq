Add LoadPath "/Users/mat/Documents/gitRepos/coq/".
Require Import objoidAndMapoid.


Arguments eq {o}.
Arguments eq_refl {o} {x}.
Arguments eq_sym {o} {x} {y}.
Arguments eq_trans {o} {x} {y} {z}.


Arguments map {a} {b}.
Arguments pres {a} {b}.
Arguments apply {a} {b}.


Infix "~" := eq (at level 80, right associativity).
Infix "|>" := apply (at level 71, left associativity).

Section po.

Structure PushOut (A B C:objoid) (f:mapoid A B) (g:mapoid A C):Type := {
    object:objoid;
    i0:mapoid B object;
    i1:mapoid C object;
    univ (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: (f||>h) = (g||>k)):
        (exists z:mapoid object Z, ((i0 ||> z) = h) /\ ((i1 ||> z) = k))
        /\
        (forall y z:mapoid object Z,(((i0 ||> z) = h) /\ ((i1 ||> z) = k) /\ ((i0 ||> y) = h) /\ ((i1 ||> y) = k)) -> z|%y)
}.

(* We define the pushout object. *)

Inductive DisjointUnion (B C:objoid):Type :=
| c: carrier C -> DisjointUnion B C
| b: carrier B -> DisjointUnion B C.

Arguments b {B} {C}.
Arguments c {B} {C}.

Inductive PushoutEq (A B C:objoid) (f:mapoid A B) (g:mapoid A C): DisjointUnion B C -> DisjointUnion B C -> Prop :=
| beq (b1 b2:carrier B) (H:b1~b2):  PushoutEq A B C f g (b b1) (b b2)
| ceq (c1 c2:carrier C) (H:c1~c2): PushoutEq A B C f g (c c1) (c c2)
| aeq (a:carrier A): PushoutEq A B C f g (b (a|>f)) (c (a|>g))
| refl: forall d1:DisjointUnion B C, PushoutEq A B C f g d1 d1
| sym (d1 d2:DisjointUnion B C) (H:PushoutEq A B C f g d1 d2): PushoutEq A B C f g d2 d1
| trans (d1 d2 d3:DisjointUnion B C) (H1:PushoutEq A B C f g d1 d2) (H2:PushoutEq A B C f g d2 d3): PushoutEq A B C f g d1 d3.

Arguments refl {A} {B} {C} {f} {g}.
Arguments sym {A} {B} {C} {f} {g}.
Arguments trans {A} {B} {C} {f} {g}.

Definition PushoutObject (A B C:objoid) (f:mapoid A B) (g:mapoid A C):objoid := {|
carrier:= DisjointUnion B C;
eq:= PushoutEq A B C f g;
eq_refl:= refl;
eq_sym:= sym;
eq_trans:= trans;
|}.

(* We define the pushout inclusions. *)

Definition ib (A B C:objoid) (f:mapoid A B) (g:mapoid A C): carrier B -> carrier (PushoutObject A B C f g) := b.

Definition mapoid_b (A B C:objoid) (f:mapoid A B) (g:mapoid A C):mapoid B (PushoutObject A B C f g) := {|
map:= ib A B C f g;
pres:= beq A B C f g
|}.

Definition ic (A B C:objoid) (f:mapoid A B) (g:mapoid A C): carrier C -> carrier (PushoutObject A B C f g) := c.

Definition mapoid_c (A B C:objoid) (f:mapoid A B) (g:mapoid A C):mapoid C (PushoutObject A B C f g) := {|
map:= ic A B C f g;
pres:= ceq A B C f g
|}.

(* We prove the universal property of the pushout. *)

Definition factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: (f||>h) |% (g||>k)) (d1:carrier (PushoutObject A B C f g)):
    carrier Z :=
    match d1 with
    | b b1 => b1 |> h
    | c c1 => c1 |> k
    end.

Lemma pres_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: (f||>h) |% (g||>k)) (d1 d2:(carrier (PushoutObject A B C f g))) (H2:d1~d2):
    factorisation A B C f g Z h k H d1 ~ factorisation A B C f g Z h k H d2.
Proof.
    elim H2.
    
    intros.
    simpl.
    apply pres.
    assumption.

    intros.
    simpl.
    apply pres.
    assumption.

    intros.
    simpl.
    apply (eq_trans (mapoid_comp_assoc f h a)).
    apply eq_sym.
    apply (eq_trans (mapoid_comp_assoc g k a)).
    apply eq_sym.
    auto.

    intros.
    apply eq_refl.

    intros.
    apply (eq_sym H1).

    intros.
    apply (eq_trans H0 H4).
Qed.
    

Definition mapoid_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: (f||>h) |% (g||>k)):
    mapoid (PushoutObject A B C f g) Z := {|
    map:=factorisation A B C f g Z h k H;
    pres:=pres_factorisation A B C f g Z h k H
    |}.

Lemma mapoid_b_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: (f||>h) |% (g||>k)):
    (mapoid_b A B C f g ||> mapoid_factorisation A B C f g Z h k H) |% h.
Proof.
    apply extensionality.
    intro.
    apply mapoid_comp_assoc.
Qed.

Lemma mapoid_c_factorisation (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: (f||>h) |% (g||>k)):
(mapoid_c A B C f g ||> mapoid_factorisation A B C f g Z h k H) |% k.
Proof.
apply extensionality.
intro.
apply mapoid_comp_assoc.
Qed.

Lemma existence_univ (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: (f||>h) |% (g||>k)):
    ((mapoid_b A B C f g ||> mapoid_factorisation A B C f g Z h k H) |% h) /\ ((mapoid_c A B C f g ||> mapoid_factorisation A B C f g Z h k H) |% k).
Proof.
    split.
    apply mapoid_b_factorisation.
    apply mapoid_c_factorisation.
Qed.

Lemma univ_pushout (A B C:objoid) (f:mapoid A B) (g:mapoid A C) (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (H: (f||>h) |% (g||>k)):
    (exists z:mapoid (PushoutObject A B C f g) Z, ((mapoid_b A B C f g ||> z) |% h) /\ ((mapoid_c A B C f g ||> z) |% k))
    /\
    (forall y z:mapoid (PushoutObject A B C f g) Z,(((mapoid_b A B C f g ||> z) |% h) /\ (((mapoid_c A B C f g) ||> z) |% k) /\ (((mapoid_b A B C f g) ||> y) |% h) /\ (((mapoid_c A B C f g) ||> y) |% k)) -> z|%y).
Proof.
    split.  
    exists (mapoid_factorisation A B C f g Z h k H ).
    split.
    apply (mapoid_b_factorisation A B C f g Z h k H).

    apply (mapoid_c_factorisation A B C f g Z h k H).

    intro.
    intro.
    intro.
    destruct H0.
    destruct H1.
    destruct H2.
    apply extensionality.
    intros.
    elim a1.
    intro.
    apply (extensionality H1).    



Section pushout.

Variables A B C Z:objoid.
Variable f:mapoid A B.
Variable g:mapoid A C.

Inductive PushoutCarrier:Type :=
| c: carrier C -> PushoutCarrier
| b: carrier B -> PushoutCarrier.

Inductive PushoutEq:PushoutCarrier -> PushoutCarrier -> Prop :=
| beq (b1 b2:carrier B) (H:b1~b2):  PushoutEq (b b1) (b b2)
| ceq (c1 c2:carrier C) (H:c1~c2): PushoutEq (c c1) (c c2)
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

Lemma pres_ib (b1 b2:carrier B) (H:b1~b2): new_b b1 ~ new_b b2.
Proof.
simpl.
apply beq.
assumption.
Qed.

Lemma pres_ic (c1 c2:carrier C) (H:c1~c2): new_c c1 ~ new_c c2.
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

Lemma pres_out (d1 d2:carrier Pushout) (H1:d1~d2): carrier_out d1 ~carrier_out d2.
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

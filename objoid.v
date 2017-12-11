Section objoid.

Require Export Coq.Classes.RelationClasses.

Structure objoid:Type :={
carrier:Type;
eq:carrier->carrier->Prop;
eq_refl (x:carrier): eq x x;
eq_sym (x y:carrier) (H:eq x y): eq y x;
eq_trans (x y z:carrier) (H1:eq x y) (H2:eq y z): eq x z
}.

Arguments eq {o}.
Arguments eq_refl {o} {x}.
Arguments eq_sym {o} {x} {y}.
Arguments eq_trans {o} {x} {y} {z}.

Infix "~" := eq (at level 80, right associativity).

Structure mapoid (a b:objoid) := {
map:carrier a-> carrier b;
pres (a1 a2:carrier a) (H:a1~a2): map a1~map a2
}.

Arguments map {a} {b}.
Arguments pres {a} {b}.

Definition apply {a b:objoid} (a1:carrier a) (f:mapoid a b) := map f a1.

Infix "|>" := apply (at level 71, left associativity).

Lemma composition_equiv {a b c:objoid} (F:mapoid a b) (G:mapoid b c) (a1 a2:carrier a) (H:a1~a2): a1 |> F |> G ~ a2 |> F |> G.
Proof.
apply pres.
apply pres.
assumption.
Qed.

Definition carrier_comp (a b c:objoid) (F:mapoid a b) (G:mapoid b c) (a1:carrier a): carrier c :=
    a1 |> F |> G.
Arguments carrier_comp {a} {b} {c}.

Definition mapoid_comp (a b c:objoid) (F:mapoid a b) (G:mapoid b c) := {|
map:= carrier_comp F G;
pres:= composition_equiv F G
|}.

Arguments mapoid_comp {a} {b} {c}.

Infix "||>" := mapoid_comp (at level 70, right associativity).

Definition mapoid_ext (a b c:objoid) (F:mapoid a b) (G:mapoid b c) (a1: carrier a) :
    (a1 |> F |> G) ~ (a1 |> (F ||> G)).
Proof.
simpl.
apply pres.
apply pres.
apply eq_refl.
Qed.

Arguments mapoid_ext {a} {b} {c}.

End objoid.

Arguments eq {o}.
Arguments eq_refl {o} {x}.
Arguments eq_sym {o} {x} {y}.
Arguments eq_trans {o} {x} {y} {z}.


Arguments map {a} {b}.
Arguments pres {a} {b}.

Arguments mapoid_comp {a} {b} {c}.
Arguments mapoid_ext {a} {b} {c}.

Infix "~" := eq (at level 80, right associativity).
Infix "|>" := apply (at level 71, left associativity).
Infix "||>" := mapoid_comp (at level 70, right associativity).

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

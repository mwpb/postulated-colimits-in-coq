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
Compute carrier_comp.
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

Variables A B C Z:objoid.
Variable f:mapoid A B.
Variable g:mapoid A C.

Inductive DCarrier:Type :=
| c: carrier C -> DCarrier
| b: carrier B -> DCarrier.

Inductive DEq:DCarrier -> DCarrier -> Prop :=
| beq (b1 b2:carrier B) (H:b1~b2):  DEq (b b1) (b b2)
| ceq (c1 c2:carrier C) (H:c1~c2): DEq (c c1) (c c2)
| aeq (a:carrier A): DEq (b (a|>f)) (c (a|>g))
| refl: forall d1:DCarrier, DEq d1 d1
| sym (d1 d2:DCarrier) (H:DEq d1 d2): DEq d2 d1
| trans (d1 d2 d3:DCarrier) (H1:DEq d1 d2) (H2:DEq d2 d3): DEq d1 d3.

Definition D:objoid := {|
carrier:=DCarrier;
eq:=DEq;
eq_refl:= refl;
eq_sym:=sym;
eq_trans:=trans
|}.

Variable h:mapoid B Z.
Variable k:mapoid C Z.

Variable H2:(f||>h) = (g||>k).

Definition carrier_out (d1:carrier D): carrier Z :=
match d1 with
| b b1 => (b1 |> h)
| c c1 => (c1 |> k)
end.

Lemma pres_out (d1 d2:carrier D) (H1:d1~d2): carrier_out d1 ~carrier_out d2.
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

Compute mapoid_out.
End objoid.


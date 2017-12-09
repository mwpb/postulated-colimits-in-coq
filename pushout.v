Variables X Y Z:Type.
Inductive DU :=
| x:X->DU
| y:Y->DU.

Variable F:X->Z.
Variable G:Y->Z.

Definition out (x:DU):Z :=
match x with
| x x1 => F(x1)
| y y1 => G(y1)
end.

Section BinRel.

Variable t:Type.
Definition Relation:=t->t->Prop.
Variable r:Relation.

Definition Reflexive :=
  forall x:t,
  r x x.

Definition Symmetric:=
  forall x y:t,
  r x y -> r y x.

Definition Transitive:=
  forall x y z:t,
  r x y -> r y z ->
  r x z.

End BinRel.

Arguments Reflexive {t}.
Arguments Transitive {t}.
Arguments Symmetric {t}.

Section Setoid.

Structure Setoid: Type:= {
  Carrier :> Type;
  Equal: Relation Carrier;
  Prf_refl : Reflexive Equal;
  Prf_trans : Transitive Equal;
  Prf_sym : Symmetric Equal}.

Arguments Equal {s}.

Lemma Equal_refl:
  forall s:Setoid,
  forall s1: Carrier s,
  Equal s1 s1.
Proof.
intros.
apply Prf_refl.
Qed.

Infix "~" := Equal (at level 80, right associativity). 

Lemma Equal_sym:
  forall s:Setoid,
  forall s1 s2:s,
  s1 ~ s2 -> s2 ~ s1.
Proof.
intros.
apply Prf_sym.
apply H.
Qed.

Lemma Equal_trans:
  forall s:Setoid,
  forall s1 s2 s3:s,
  s1~s2 -> s2~s3 -> s1~s3.
Proof.
intro.
apply Prf_trans.
Qed.

End Setoid.

Arguments Equal {s}.
Arguments Prf_trans {s} {x} {y} {z}.
Arguments Prf_refl {s} {x}.
Arguments Prf_sym {s} {x} {y}.

Infix "~" := Equal (at level 80, right associativity). 

Section Mapoids.

Variables s s' s'':Setoid.

Definition MapLaw (f:s->s') :=
  forall s1 s2:s,
  s1~s2 -> (f s1)~(f s2).

Structure Mapoid: Type := {
  Map:> s->s';
  Prf_pres: MapLaw Map}.

End Mapoids.

Section Ext.

Variables s s':Setoid.

Definition mapoid_sim (f:Mapoid s s') (g:Mapoid s s'):=
  forall s1:s,
  f s1 ~ g s1.

Definition id_fn (s:Setoid) := fun x:s => x.

Lemma id_pres (t:Setoid): MapLaw t t (fun x => x).
Proof.
intro.
intro.
intro.
apply H.
Qed.

Definition id_mapoid (s:Setoid) : Mapoid s s := {|
  Map := id_fn s;
  Prf_pres := id_pres s|}.

Infix "\" := mapoid_sim (at level 80, right associativity). 

End Ext.

Arguments mapoid_sim {s} {s'}.

Section Composition.

Variables s s' s'':Setoid.

Lemma law_comp (f:Mapoid s s') (g:Mapoid s' s''):
  MapLaw s s'' (fun x => g (f x)).
Proof.
intro.
intro.
intro.
apply Prf_pres.
apply Prf_pres.
apply H.
Qed.

Definition comp (f:Mapoid s s') (g:Mapoid s' s'') := {|
  Map := fun x => g (f x);
  Prf_pres := law_comp f g|}.

End Composition.

Arguments comp {s} {s'} {s''}.

Section GenEq.

Variable A:Type.
Variable R: A -> A -> Prop.

Inductive gen_equiv : A -> A -> Prop :=
  | inc (a b:A): (R a b) -> gen_equiv a b
  | refl (a:A): gen_equiv a a
  | sym (a b:A): gen_equiv a b -> gen_equiv b a
  | trans (a b c:A): gen_equiv a b -> gen_equiv b c -> gen_equiv a c.

Lemma gen_equiv_refl: Reflexive gen_equiv.
Proof.
intro.
apply refl.
Qed.
Lemma gen_equiv_trans: Transitive gen_equiv.
Proof.
intro.
apply trans.
Qed.
Lemma gen_equiv_sym: Symmetric gen_equiv.
Proof.
intro.
apply sym.
Qed.

End GenEq.

Section GenSetoid.

Arguments gen_equiv {A}.
Arguments gen_equiv_refl {A} {R}.
Arguments gen_equiv_sym {A} {R}.
Arguments gen_equiv_trans {A} {R}.

Variable A:Type.
Variable R: A -> A -> Prop.


Definition gen_setoid : Setoid :=
{|
  Carrier := A;
  Equal := gen_equiv R;
  Prf_refl := gen_equiv_refl;
  Prf_trans := gen_equiv_trans;
  Prf_sym := gen_equiv_sym
|}.

End GenSetoid.

Section Test.

Variables a b c:Setoid.
Variable f:Mapoid a b.
Variable g:Mapoid a c.

Inductive d0 : Type :=
  | iota_b: b->d0
  | iota_c: c->d0.

Inductive d0eq: d0 -> d0 -> Prop :=
  | inc_b (b1 b2:b): b1~b2 -> d0eq (iota_b b1) (iota_b b2)
  | inc_c (c1 c2:c): c1~c2 -> d0eq (iota_c c1) (iota_c c2)
  | inc_a (x:a): d0eq (iota_b (f x)) (iota_c (g x)).

Definition d := gen_setoid d0 d0eq.

End Test.

Section Category.

Structure Category :Type := {
  obj: Setoid;
  arr: Setoid;
  source: Mapoid arr obj;
  target: Mapoid arr obj;
  id: Mapoid obj arr;
  section_s (x:obj): x~source (id x);
  section_t (x:obj): target (id x)~x;
  mult (f g:arr): (target f ~ source g) -> arr;
  mult_t (f g:arr) (H: target f ~ source g): target (mult f g H) ~ target g;
  mult_s (f g:arr) (H: target f ~ source g): source (mult f g H) ~ source f;
  left_id (f:arr): (mult (id (source f)) f (section_t (source f))) ~ f;
  right_id (f:arr): (mult f (id (target f)) (section_s (target f))) ~ f;
  assoc (f g h:arr) (H1:target f~source g) (H2:target g~source h):
    mult (mult f g H1) h (Prf_trans (mult_t f g H1) H2) ~ mult f (mult g h H2) (Prf_trans H1 (Prf_sym (mult_s g h H2)))
  }.

End Category.

Arguments source {c}.
Arguments target {c}.
Arguments id {c}.
Arguments mult {c}.

Section FunctorData.

Variables C D: Category.
Variable ArrMap: Mapoid (arr C) (arr D).
Variable ObjMap: Mapoid (obj C) (obj D).
Variables f g:arr C.
Variable x:obj C.

Variable Pres_s: ObjMap (source f)~source (ArrMap f).
Variable Pres_t: target (ArrMap f)~ObjMap (target f).
Variable Pres_id: id (ObjMap x)~ArrMap (id x).

Variable composable: target f ~ source g.

Lemma Pres_composable: target (ArrMap f)~source (ArrMap g).
Proof.
apply Prf_sym.
apply (Prf_trans Pres_t).

Section Functor.

Structure Functor (C:Category) (D:Category) : Type := {
  ArrMap: Mapoid (arr C) (arr D);
  ObjMap: Mapoid (obj C) (obj D);
  Pres_s (f:arr C): source (ArrMap f)~ObjMap (source f);
  Pres_t (f:arr C): target (ArrMap f)~ObjMap (target f);
  Pres_id (x:obj C): id (ObjMap x)~ArrMap (id x);
  Pres_mul (f g:arr C) (H:target f~source g): (ArrMap (mult f g H))~ mult (ArrMap f) (ArrMap g)
}.

















Section objoid.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Record objoid: Type :=
  {carrier:>Type;
   eq:carrier->carrier->Prop;
   refl: reflexive carrier eq;
   sym: symmetric carrier eq;
   trans: transitive carrier eq}.

Arguments eq {o}.
Infix "~" := eq (at level 95).

Structure mapd (A B:objoid) :=
  {map:> carrier A -> carrier B;
   pres (a1 a2:carrier A) (H:a1~a2): map a1~map a2}.

Variables A B C:objoid.
Arguments map {A}{B}.
Variables f f2:mapd A B.
Variable g:mapd B C.

Lemma comp_pres{X Y Z:objoid}{F:mapd X Y}{G:mapd Y Z}:
  forall a1 a2: carrier X,
    (a1~a2)->
    G(F(a1))~G(F(a2)).
Proof.
  intros. apply pres. apply pres. apply H. Qed.

Definition application (a1:carrier A) (f1:mapd A B) := map f1 a1.
Definition comp{X Y Z:objoid}(F:mapd X Y)(G:mapd Y Z):=
  {|map:=fun a:carrier X=>G(F(a));
    pres:=comp_pres|}.

Axiom mapd_ext:
  (forall a:carrier A, f(a)~f2(a)) -> f=f2.

Definition mapd_eq {X Y:objoid}: mapd X Y -> mapd X Y -> Prop:=
  (fun f g => forall a:X, f a ~ g a).

Lemma mapd_eq_refl{X Y:objoid}:
  forall f:mapd X Y,
    mapd_eq f f.
Proof.
  unfold mapd_eq. intros. apply refl. Qed.

Lemma mapd_eq_sym{X Y:objoid}:
  forall f g:mapd X Y,
    mapd_eq f g ->
    mapd_eq g f.
Proof.
  unfold mapd_eq. intros. apply sym. apply H. Qed.

Lemma mapd_eq_trans{X Y:objoid}:
  forall f g h:mapd X Y,
    mapd_eq f g->
    mapd_eq g h->
    mapd_eq f h.
Proof.
  unfold mapd_eq. intros. specialize H0 with (a:=a).
  specialize H with a. revert H0. revert H. apply trans. Qed.

Definition mapoid (X Y:objoid):=
  {|carrier:=mapd X Y;
   eq:=mapd_eq;
   refl:=mapd_eq_refl;
   sym:=mapd_eq_sym;
   trans:=mapd_eq_trans|}.
Check comp.
Definition compn (X Y Z:objoid) (F:mapoid X Y) (G:mapoid Y Z):mapoid X Z:=
  comp F G.
Axiom mapoid_app:
  forall (X Y:objoid) (F G:mapoid X Y),
    F~G -> (forall a:carrier X, F(a)~G(a)).


End objoid.

Add Parametric Relation (s : objoid) : (@carrier s) (@eq s)
       reflexivity proved by (refl s)
       symmetry proved by (sym s)
       transitivity proved by (trans s) as eq_rel.
Arguments eq {o}.
Infix "~" := eq (at level 95).
Add Parametric Morphism (S1 S2 S3:objoid) (M:mapoid S1 S2):
  (@compn S1 S2 S3 M) with signature (@eq (mapoid S2 S3) ==> @eq (mapoid S1 S3)) as apply_compn.
Proof.
  intros. unfold compn. simpl. unfold mapd_eq. intros. simpl.
  simpl in H. unfold mapd_eq in H. apply H. Qed.
Check compn.
Add Parametric Morphism (S1 S2:objoid) (M:mapoid S1 S2):
  (@map S1 S2 M) with signature (@eq S1 ==> @eq S2) as apply_mor.
Proof. apply pres. Qed.

Arguments map {A} {B}.
Arguments pres {A} {B}.
(* Arguments mapoid_ext {A}{B}. *)
Arguments mapoid_app {X}{Y}{F}{G}.
Arguments sym {o}{x}{y}.
Arguments refl {o}{x}.
Arguments trans {o}{x}{y}{z}.
Arguments application {A} {B}.
(* Arguments compn {A}{B}{C}. *)
Arguments compn{X}{Y}{Z}.
Infix "|>" := application (at level 11, left associativity).
Infix "||>" := compn (at level 10, right associativity).
(* Arguments mapoid_eq{A}{B}. *)
Lemma compn_assoc:
  forall (A B C D:objoid)(F:mapoid A B)(G:mapoid B C)(H:mapoid C D),
    mapd_eq (F||>G||>H) ((F||>G)||>H).
Proof.
  unfold mapd_eq. intros. simpl. reflexivity. Qed.
Arguments compn_assoc{A}{B}{C}{D}{F}{G}.

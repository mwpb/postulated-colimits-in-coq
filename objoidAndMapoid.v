Section objoid.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

(*  an objoid is like a setoid but we don't have to carry around
    the Type of the carrier *)
Record objoid: Type :=
      { carrier:>Type;
        eq:carrier->carrier->Prop;
        refl: reflexive _ eq;
        sym: symmetric _ eq;
        trans: transitive _ eq
      }.

Arguments eq {o}.
Infix "~" := eq (at level 95).
Variables A B C:objoid.

(*  a mapoid is a function between the carriers of two objoids
    that preserves the equivalence *)
Structure mapoid (A B:objoid) :=
  {map:> carrier A -> carrier B;
   pres (a1 a2:carrier A) (H:a1~a2): map a1~map a2}.

Arguments map {A}{B}.

Variable f:mapoid A B.
Variable f2:mapoid A B.
Variable g:mapoid B C.

Lemma comp_pres:
  forall a1 a2: carrier A,
    (a1~a2)->
    g(f(a1))~g(f(a2)).
Proof.
  intros. apply pres. apply pres. apply H. Qed.

Definition apply (a1:carrier A) (f1:mapoid A B) := map f1 a1.
Definition comp:=
  {|map:=fun a:carrier A=>g(f(a));
    pres:=comp_pres|}.

Axiom mapoid_ext:
  (forall a:carrier A, f(a)~f2(a)) -> f=f2.
Axiom mapoid_app:
  f=f2 -> (forall a:carrier A, f(a)~f2(a)).

End objoid.

Add Parametric Relation (s : objoid) : (@carrier s) (@eq s)
       reflexivity proved by (refl s)
       symmetry proved by (sym s)
       transitivity proved by (trans s) as eq_rel.

Arguments eq {o}.
Infix "~" := eq (at level 95).
Add Parametric Morphism (S1 S2:objoid) (M:mapoid S1 S2):
  (@map S1 S2 M) with signature (@eq S1 ==> @eq S2) as apply_mor.
Proof. apply pres. Qed.

Arguments map {A} {B}.
Arguments pres {A} {B}.
Arguments mapoid_ext {A}{B}.
Arguments mapoid_app {A}{B}{f}{f2}.
Arguments sym {o}{x}{y}.

Arguments apply {A} {B}.
Arguments comp {A}{B}{C}.
Infix "|>" := apply (at level 11, left associativity).
Infix "||>" := comp (at level 10, right associativity).

Section generators.

Variable A:Type.
Variable rel:relation A.

Inductive gen_equiv:relation A:=
|from_rel (a1 a2:A):(rel a1 a2)->gen_equiv a1 a2
|gen_refl (a1:A):gen_equiv a1 a1
|gen_sym (a1 a2:A):gen_equiv a1 a2 -> gen_equiv a2 a1
|gen_trans (a1 a2 a3:A):gen_equiv a1 a2->gen_equiv a2 a3->gen_equiv a1 a3.

Lemma gen_equiv_refl: Reflexive gen_equiv.
Proof.
  unfold Reflexive. intros. apply gen_refl. Qed.
Lemma gen_equiv_sym: Symmetric gen_equiv.
Proof.
  unfold Symmetric. intros. apply gen_sym. apply H. Qed.
Lemma gen_equiv_trans: Transitive gen_equiv.
Proof.
  unfold Transitive. intro. intro. intro. apply gen_trans. Qed.

Program Instance gen_setoid_inner: Setoid A:=
  {equiv:=gen_equiv;
    setoid_equiv:=
      {|Equivalence_Reflexive:=gen_equiv_refl;
        Equivalence_Symmetric:=gen_equiv_sym;
        Equivalence_Transitive:=gen_equiv_trans|}}.

Definition gen_obj:objoid :=
  {|carrier:=A;
    eq:=gen_equiv;
    refl:=gen_refl;
    sym:=gen_sym;
    trans:=gen_trans|}.

End generators.

Arguments gen_obj{A}.

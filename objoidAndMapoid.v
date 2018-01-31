Section objoid.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

(*  an objoid is like a setoid but we don't have to carry around
    the Type of the carrier *)
Structure objoid := {
    carrier:>Type;
    eq: Setoid carrier
}.

(*  a mapoid is a function between the carriers of two objoids
    that preserves the equivalence *)
Structure mapoid (A B: objoid) := {
    map:> A -> B;
    pres (a1 a2:A) (H:a1=a2): map a1=map a2
}.

Arguments map {A} {B}.

Definition apply (A B: objoid) (a1:A) (f:mapoid A B) := map f a1.

End objoid.

Arguments map {A} {B}.
Arguments pres {A} {B}.

Arguments apply {A} {B}.
Infix "|>" := apply (at level 11, left associativity).

Section generators.

Variable A:Type.
Variable rel:relation A.

Inductive gen_equiv:A->A->Prop:=
|from_rel (a1 a2:A):(rel a1 a2)->gen_equiv a1 a2
|refl (a1:A):gen_equiv a1 a1
|sym (a1 a2:A):gen_equiv a1 a2 -> gen_equiv a2 a1
|trans (a1 a2 a3:A):gen_equiv a1 a2->gen_equiv a2 a3->gen_equiv a1 a3.

Lemma gen_equiv_refl: Reflexive gen_equiv.
Proof.
  unfold Reflexive. intros. apply refl. Qed.
Lemma gen_equiv_sym: Symmetric gen_equiv.
Proof.
  unfold Symmetric. intros. apply sym. apply H. Qed.
Lemma gen_equiv_trans: Transitive gen_equiv.
Proof.
  unfold Transitive. intro. intro. intro. apply trans. Qed. 

Program Instance gen_setoid_inner: Setoid A:=
  {equiv:=gen_equiv;
    setoid_equiv:=
      {|Equivalence_Reflexive:=gen_equiv_refl;
        Equivalence_Symmetric:=gen_equiv_sym;
        Equivalence_Transitive:=gen_equiv_trans|}}.

Definition gen_obj:objoid :=
  {|carrier:=A;
    eq:=gen_setoid_inner|}.

End generators.

Arguments gen_obj{A}.
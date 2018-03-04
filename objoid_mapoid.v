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

Structure mapoid (A B:objoid) :=
  {map:> carrier A -> carrier B;
   pres (a1 a2:carrier A) (H:a1~a2): map a1~map a2}.

Variables A B C:objoid.
Arguments map {A}{B}.
Variables f f2:mapoid A B.
Variable g:mapoid B C.

Lemma comp_pres:
  forall a1 a2: carrier A,
    (a1~a2)->
    g(f(a1))~g(f(a2)).
Proof.
  intros. apply pres. apply pres. apply H. Qed.

Definition application (a1:carrier A) (f1:mapoid A B) := map f1 a1.
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
Arguments refl {o}{x}.
Arguments application {A} {B}.
Arguments comp {A}{B}{C}.
Infix "|>" := application (at level 11, left associativity).
Infix "||>" := comp (at level 10, right associativity).
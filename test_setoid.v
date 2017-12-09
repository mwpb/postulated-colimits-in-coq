Require Export Setoid.
Require Export Relation_Definitions.

Parameter set: Type -> Type.
Parameter empty: forall A, set A.
Parameter eq_set: forall A, relation A.

Axiom eq_set_refl: forall A, reflexive A (eq_set A).
Axiom eq_set_sym: forall A, symmetric A (eq_set A).
Axiom eq_set_trans: forall A, transitive A (eq_set A).

Add Parametric Relation A: (set A) (@eq_set A)
  reflexivity proved by eq_set_refl
  symmetry proved by eq_set_sym
  transitivity proved by eq_set_trans
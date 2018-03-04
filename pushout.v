Require Import objoid_mapoid.
Require Import coequaliser.
Require Import disjoint_union.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Equality.

Section pushout.

  Variables A B C:objoid.
  Variable f:mapoid A B.
  Variable g:mapoid A C.

  Structure Pushout:Type :=
    {po_obj:objoid;
     i0:mapoid B po_obj;
     i1:mapoid C po_obj;
     commutes: f||>i0 = g||>i1;
     po_induced:
       forall (Z:objoid) (h:mapoid B Z) (k:mapoid C Z)
              (H:f ||> h = g ||> k),
         mapoid po_obj Z;
     po_fact:
       forall (Z:objoid) (h:mapoid B Z) (k:mapoid C Z)
              (H:f ||> h = g ||> k),
         (i0||>(po_induced Z h k H)=h)/\
         (i1||>(po_induced Z h k H)=k);
     po_unique:
       forall (Z:objoid) (x y:mapoid po_obj Z),
         (i0||>x=i0||>y)/\
         (i1||>x=i1||>y)->
         x=y}.

  Definition BuC:disjoint_union B C:=
    mk_du B C.
Check mk_coequaliser.
  Definition coeq:coequaliser A (du_obj BuC) (f||>(u0 BuC)) (g||>(u1 BuC)):=
    mk_coequaliser A (du_obj BuC) (f||>(u0 BuC)) (g||>(u1 BuC)).
  Lemma prf_commutes:
    f||>(u0 BuC||>(coeq_arr coeq))=g||>(u1 BuC||>(coeq_arr coeq)).
  Proof.
    apply mapoid_ext. intro.
    assert (H:(f ||> u0 BuC) ||> coeq_arr coeq = (g ||> u1 BuC) ||> coeq_arr coeq).
    - apply (cofork coeq).
    - apply mapoid_app with a in H. assumption. Qed.

  Lemma can_invoke_coeq (Z:objoid) (h:mapoid B Z)
             (k:mapoid C Z) (H:f ||> h = g ||> k):
    (f ||> u0 BuC) ||> du_induced BuC Z h k =
    (g ||> u1 BuC) ||> du_induced BuC Z h k.
  Proof.
    apply mapoid_ext. intros. simpl.
    apply mapoid_app with a in H. simpl in H. assumption. Qed.
  
  Definition prf_po_induced (Z:objoid) (h:mapoid B Z)
             (k:mapoid C Z) (H:f ||> h = g ||> k):
    mapoid (coeq_obj coeq) Z:=
    (coeq_induced coeq) Z (du_induced BuC Z h k) (can_invoke_coeq Z h k H).

  Lemma prf_po_fact (Z:objoid) (h:mapoid B Z)
        (k:mapoid C Z) (H:f ||> h = g ||> k):
    ((u0 BuC||>(coeq_arr coeq))||>(prf_po_induced Z h k H)=h/\
     ((u1 BuC||>(coeq_arr coeq))||>(prf_po_induced Z h k H)=k)).
  Proof.
    intros. split.
    - apply mapoid_ext. intros. simpl. apply refl.
    - apply mapoid_ext. intros. simpl. apply refl.
  Qed.

  Lemma prf_po_unique:
    forall (Z:objoid) (x y:mapoid (coeq_obj coeq) Z),
         ((u0 BuC||>(coeq_arr coeq))||>x=(u0 BuC||>(coeq_arr coeq))||>y)/\
         ((u1 BuC||>(coeq_arr coeq))||>x=(u1 BuC||>(coeq_arr coeq))||>y)->
  x=y.
  Proof.
    intros. destruct H as (H0&H1). apply mapoid_ext. intros.
    induction a.
    - apply mapoid_app with c in H0. simpl in H0. assumption.
    - apply mapoid_app with c in H1. simpl in H1. assumption.
  Qed.
    
  Definition mk_pushout:=
    {|po_obj:=(coeq_obj coeq);
      i0:=u0 BuC||>(coeq_arr coeq);
      i1:=u1 BuC||>(coeq_arr coeq);
      commutes:=prf_commutes;
      po_induced:=prf_po_induced;
      po_fact:=prf_po_fact;
      po_unique:=prf_po_unique|}.

End pushout.

Arguments mk_pushout {A}{B}{C}.
Arguments i0 {A}{B}{C}{f}{g}.
Arguments i1 {A}{B}{C}{f}{g}.
Arguments commutes {A}{B}{C}{f}{g}.
Arguments po_obj {A}{B}{C}{f}{g}.
Arguments po_induced {A}{B}{C}{f}{g}.
Arguments po_fact {A}{B}{C}{f}{g}.
Arguments po_unique {A}{B}{C}{f}{g}.
Arguments BuC {B}{C}.
(* Arguments BuC {B}{C}. *)


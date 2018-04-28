Require Import objoid_mapoid.
Require Import coequaliser.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Section disjoint_union.

  Variables B C:objoid.

  Structure disjoint_union:Type:=
    {du_obj:objoid;
     u0:mapoid B du_obj;
     u1:mapoid C du_obj;
     du_induced:
       forall (Z:objoid) (h:mapoid B Z) (k:mapoid C Z),
         mapoid du_obj Z;
     du_fact:
       forall (Z:objoid) (h:mapoid B Z) (k:mapoid C Z),
         ((u0||>(du_induced Z h k)) ~ h)
           /\(u1||>(du_induced Z h k)~k);
     du_unique:
       forall (Z:objoid) (x y:mapoid du_obj Z),
         (u0||>x~u0||>y)/\(u1||>x~u1||>y)->
         x~y}.
  
  Inductive du:Type :=
  |b:B -> du
  |c:C -> du.

  Inductive du_eq:relation du:=
  |beq(b1 b2:B) (H:b1~b2):du_eq (b b1) (b b2)
  |ceq(c1 c2:C) (H:c1~c2):du_eq (c c1) (c c2).
                                      
  Lemma du_refl:
    forall x:du,
      du_eq x x.
  Proof.
    intros. induction x.
    - apply beq. apply refl.
    - apply ceq. apply refl. Qed.
  Lemma du_sym:
    forall x y:du,
      du_eq x y->
      du_eq y x.
  Proof.
    intros. induction H.
    - apply beq. apply sym. assumption.
    - apply ceq. apply sym. assumption. Qed.

  Lemma du_trans:
    forall x1 x2 x3:du,
      du_eq x1 x2->du_eq x2 x3->
      du_eq x1 x3.
  Proof.
    intros. induction H.
    - inversion H0.
      -- apply beq. revert H2. revert H. apply trans.
    - inversion H0.
      -- apply ceq. revert H2. revert H. apply trans. Qed.
    
  Definition du_objoid:objoid:=
    {|carrier:=du;
      eq:=du_eq;
      refl:=du_refl;
      sym:=du_sym;
      trans:=du_trans|}.

  Add Parametric Morphism:
    (@b) with signature (@eq B ==> @eq du_objoid) as apply_b.
  Proof.
    intros. apply beq. assumption. Qed.

  Lemma b_pres:
    forall b1 b2:B,
      b1~b2 ->
      (b(b1):(carrier du_objoid)) ~ (b(b2):(carrier du_objoid)).
    Proof.
    intros. simpl. apply beq. assumption. Qed.

  Definition mapoid_b: mapoid B du_objoid :=
    {|map:= fun (b1:B)=>b(b1):(carrier du_objoid);
      pres:= b_pres|}.

  Add Parametric Morphism:
    (@c) with signature (@eq C ==> @eq du_objoid) as apply_c.
  Proof.
    intros. apply ceq. assumption. Qed.

  Lemma c_pres:
    forall c1 c2:C,
      c1~c2->
      (c c1:(carrier du_objoid))~(c c2).
  Proof.
    intros. apply ceq. assumption. Qed.
  
  Definition mapoid_c:=
    {|map:= fun (c1:C)=>(c c1):carrier du_objoid;
      pres:= c_pres|}.

  Definition du_fact_map(Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (x:du_objoid):Z:=
    match x with
    |b b1=>h(b1)
    |c c1=> k(c1)
    end.
  Lemma du_fact_pres(Z:objoid) (h:mapoid B Z) (k:mapoid C Z):
    forall x1 x2:du_objoid,
      x1~x2->
      du_fact_map Z h k x1 ~ du_fact_map Z h k x2.
  Proof.
    intros. induction H.
    - simpl. apply pres. assumption.
    - simpl. apply pres. assumption. Qed.
  
  Definition du_factorisation(Z:objoid) (h:mapoid B Z) (k:mapoid C Z):mapoid du_objoid Z:=
    {|map:=du_fact_map Z h k;
      pres:=du_fact_pres Z h k|}.

  Lemma prf_du_fact:
    forall (Z:objoid) (h:mapoid B Z) (k:mapoid C Z),
      ((mapoid_b||>(du_factorisation Z h k)) ~ h)
      /\(mapoid_c||>(du_factorisation Z h k)~k).
  Proof.
    intros. split.
    - intros. simpl. unfold mapd_eq. simpl. intro. apply refl.
    - intros. simpl. unfold mapd_eq. intro. apply refl. Qed.
  
  Lemma prf_du_unique:
    forall (Z:objoid) (x y:mapoid du_objoid Z),
      (mapoid_b||>x~mapoid_b||>y)/\(mapoid_c||>x~mapoid_c||>y)->
      x~y.
  Proof.
    intros. simpl. unfold mapd_eq. intros. destruct H as (H0&H1).
    induction a.
    - apply mapoid_app with c0 in H0. simpl in H0. assumption.
    - apply mapoid_app with c0 in H1. simpl in H1. assumption.
      Qed.
  
  Definition mk_du:disjoint_union:=
    {|du_obj:=du_objoid;
      u0:=mapoid_b;
      u1:=mapoid_c;
      du_induced:=du_factorisation;
      du_fact:=prf_du_fact;
      du_unique:=prf_du_unique|}.

End disjoint_union.

Arguments du_obj {B}{C}.
Arguments u0 {B}{C}.
Arguments u1 {B}{C}.
Arguments du_induced {B}{C}.
Arguments du_fact {B}{C}.
Arguments du_unique {B}{C}.
Arguments c{B}{C}.
Arguments b{B}{C}.
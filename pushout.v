(*
  In emacs use
     (setq coq-compile-before-require t)
     (setq coq-load-path-include-current t)
  in init file.
*)

Require Import objoidAndMapoid.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Section pushout.

  Variables A B C:objoid.
  Variable f:mapoid A B.
  Variable g:mapoid A C.

  Structure Pushout:Type :=
    {object:objoid;
     i0:mapoid B object;
     i1:mapoid C object;
     commutes: f||>i0 = g||>i1;
     univ:
       forall (Z:objoid) (h:mapoid B Z) (k:mapoid C Z),
         f ||> h = g ||> k ->
         (exists! z:mapoid object Z,
             ( i0 ||> z = h) /\ ( i1 ||> z = k))}.

  Inductive DisjointUnion:Type :=
  |b:B -> DisjointUnion
  |c:C -> DisjointUnion.

  Inductive PushoutEq: relation DisjointUnion :=
  |aeq(a1:carrier A): PushoutEq (b (f(a1))) (c (g(a1)))
  |beq(b1 b2:carrier B) (H:b1~b2): PushoutEq (b b1) (b b2)
  |ceq(c1 c2:carrier C) (H:c1~c2): PushoutEq (c c1) (c c2)
  |gen_refl (a1:DisjointUnion):PushoutEq a1 a1
  |gen_sym (a1 a2:DisjointUnion):PushoutEq a1 a2 ->PushoutEq a2 a1
  |gen_trans (a1 a2 a3:DisjointUnion):PushoutEq a1 a2->PushoutEq a2 a3->PushoutEq a1 a3.

  Definition pushout_objoid:objoid:=
    {|carrier:=DisjointUnion;
      eq:=PushoutEq;
      refl:=gen_refl;
      sym:=gen_sym;
      trans:=gen_trans|}.
  
  Lemma b_pres:
    forall b1 b2:B,
      b1~b2 ->
      (b(b1):(carrier pushout_objoid)) ~ (b(b2):(carrier pushout_objoid)).
  Proof.
    intros. simpl. apply beq. assumption. Qed.

  Definition mapoid_b: mapoid B pushout_objoid :=
    {|map:= fun (b1:B)=>b(b1):(carrier pushout_objoid);
      pres:= b_pres|}.
  
  Lemma c_pres:
    forall c1 c2:C,
      c1~c2->
      (c c1:(carrier pushout_objoid))~(c c2).
  Proof.
    intros. apply ceq. assumption. Qed.
  
  Definition mapoid_c:=
    {|map:= fun (c1:C)=>(c c1):carrier pushout_objoid;
      pres:= c_pres|}.

  Section factorisation.
  Variable Z:objoid.
  Variable h:mapoid B Z.
  Variable k:mapoid C Z.
  Variable outer: (comp f h) = (comp g k).
  
  Definition factorisation (d1:pushout_objoid):=
    match d1 with
    | b b1 => (b1 |> h)
    | c c1 => (c1 |> k)
    end.

  Lemma pres_factorisation:
    forall d1 d2:pushout_objoid,
      d1~d2 ->
      factorisation d1 ~ factorisation d2.
  Proof.
    intros. simpl in H. dependent induction H.
    - apply mapoid_app with a1 in outer. simpl. simpl in outer. assumption.
    - apply pres. assumption.
    - apply pres. assumption.
    - apply refl.
    - apply sym in IHPushoutEq. assumption.
    - revert IHPushoutEq2. revert IHPushoutEq1. apply trans. Qed.
      
  Definition mapoid_factorisation:
    mapoid pushout_objoid Z :=
    {|map:=factorisation;
      pres:=pres_factorisation|}.
  End factorisation.

Arguments mapoid_factorisation {Z}{h}{k}.

  Proposition proof_univ:
    forall (Z:objoid) (h:mapoid B Z) (k:mapoid C Z) (outer:         f ||> h = g ||> k),
    (exists! z:mapoid pushout_objoid Z,
        ( mapoid_b ||> z = h) /\ ( mapoid_c ||> z = k)).
  Proof.
    intros. unfold unique. exists (mapoid_factorisation outer). split.
    - split.
      -- unfold mapoid_factorisation. unfold mapoid_b. unfold comp.
         simpl. apply mapoid_ext. simpl. reflexivity.
      -- unfold mapoid_factorisation. unfold mapoid_c. unfold comp.
         simpl. apply mapoid_ext. simpl. reflexivity.            
    - intros. apply mapoid_ext. intro d. destruct H as(H0&H1).
      induction d.
      -- unfold mapoid_factorisation. simpl. rewrite <- H0. reflexivity.
      -- unfold mapoid_factorisation. simpl. rewrite <- H1. reflexivity.
         Qed.

   Lemma proof_commutes:
     f||>mapoid_b = g||>mapoid_c.
   Proof.
     apply mapoid_ext. simpl. apply aeq. Qed.

Definition mk_pushout: Pushout:= {|
        object := pushout_objoid;
        i0 := mapoid_b;
        i1 := mapoid_c;
        univ :=proof_univ;
        commutes:=proof_commutes|}.

End pushout.

Arguments mk_pushout {A}{B}{C}.
Arguments i1 {A}{B}{C}{f}{g}.
Arguments PushoutEq {A}{B}{C}.
Arguments mapoid_c {A}{B}{C}.

Section TestPushout.
  
Variables A B C D:objoid.
Variable f:mapoid A B.
Variable g:mapoid A C.
Variable H:
  forall a1 a2:A,
    a1|>f=a2|>f ->
    a1=a2.

Definition P := mk_pushout f g.

Proposition mapoid_c_mono:
  forall c1 c2:C,
    c1|>mapoid_c f g=c2|>mapoid_c f g ->
    c1=c2.
Proof.
  intros. dependent induction H0. reflexivity. Qed.

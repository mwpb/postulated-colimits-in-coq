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
  
  (* Inductive blist:B->DisjointUnion->Type:= *)
  (* |singleB (b1:B):blist b1 (b b1) *)
  (* |consB (c1:C) (x1:DisjointUnion) (m:clist c1 x1) (a1:A) (H2:g(a1)=c1):blist (f(a1)) x1 *)
  (* with clist:C->DisjointUnion->Type:= *)
  (* |singleC (c1:C):clist c1 (c c1) *)
  (* |consC (b1:B) (x1:DisjointUnion) (a1:A) (H:f(a1)=b1):clist (g(a1)) x1. *)

  Record PType:Type:=
    {car:>Type;
     pt:car}.

  Record PFunc (X Y:PType):Type:=
    {func:>X->Y;
     preserves:func(pt X)=pt Y}.

  (* Need to restrict to only those spans allowed by colimit. *)
  Record span (First Last:PType):Type:=
    {Rel:PType;
     S0:PFunc Rel First;
     S1:PFunc Rel Last}.

  Arguments Rel {First}{Last}.
  Arguments S0 {First}{Last}.
  Arguments S1 {First}{Last}.
  
  Inductive zigzag (X Y:PType):Type:=
  |PId:span X Y->zigzag X Y
  |PCons {W:PType}: span X W -> zigzag W Y -> zigzag X Y.

  Fixpoint appd_zigzag {A B C:PType} (z1:zigzag A B) (z2:zigzag B C):zigzag A C:=
    match z1 with
    |PId _ _ s => PCons _ _ s z2
    |PCons _ _ s t => PCons _ _ s (appd_zigzag t z2)
    end.
  
  Definition rev_span {X Y:PType} (s:span X Y):span Y X:=
    {|Rel:=Rel s;
      S0:=S1 s;
      S1:=S0 s|}.
  
  Fixpoint rev_zigzag {X Y:PType} (z1:zigzag X Y):zigzag Y X:=
    match z1 with
    |PId _ _ s => PId _ _ (rev_span s)
    |PCons _ _ s t=> appd_zigzag (rev_zigzag t) (PId _ _ (rev_span s))
    end.  
            
  (* Inductive zz:relation DisjointUnion:= *)
  (* |bin (b1:B) (x1:DisjointUnion) (l:blist b1 x1): zz (b b1) x1 *)
  (* |cin (c1:C) (x1:DisjointUnion) (l:clist c1 x1): zz (c c1) x1. *)
     
  (* Inductive PushoutEq: relation DisjointUnion := *)
  (* |aeq(a1:carrier A): PushoutEq (b (f(a1))) (c (g(a1))) *)
  (* |beq(b1 b2:carrier B) (H:b1~b2): PushoutEq (b b1) (b b2) *)
  (* |ceq(c1 c2:carrier C) (H:c1~c2): PushoutEq (c c1) (c c2) *)
  (* |gen_refl (a1:DisjointUnion):PushoutEq a1 a1 *)
  (* |gen_sym (a1 a2:DisjointUnion):PushoutEq a1 a2 ->PushoutEq a2 a1 *)
  (* |gen_trans (a1 a2 a3:DisjointUnion):PushoutEq a1 a2->PushoutEq a2 a3->PushoutEq a1 a3. *)


  Lemma id_preserves_pt (X:PType):
      (fun x=>x)(pt X) = pt X.
  Proof. reflexivity. Qed.
  Definition id_PFunc (X:PType):=
    {|func:=fun x => x;
      preserves:=id_preserves_pt X|}.
  Definition refl_span (X:PType):span X X:=
    {|Rel:=X;
      S0:=id_PFunc X;
      S1:=id_PFunc X|}.
  Definition refl_zigzag (X:PType):=
    PId _ _ (refl_span X).

  Lemma zigzag_refl:
    forall X:PType,
      zigzag X X.
  Proof.
    intro. apply refl_zigzag. Qed.

  Lemma zigzag_sym:
    forall X Y:PType,
      zigzag X Y ->
      zigzag Y X.
  Proof.
    intros. apply rev_zigzag. assumption. Qed.

  Lemma zigzag_trans:
    forall X Y Z:PType,
      zigzag X Y -> zigzag Y Z ->
      zigzag X Z.
  Proof.
    intros X Y Z. apply appd_zigzag. Qed.
  
  Definition pushout_objoid:objoid:=
    {|carrier:=DisjointUnion;
      eq:=zz;
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
    a1|>f~a2|>f ->
    a1~a2.

Definition P := mk_pushout f g.

Proposition mapoid_c_mono:
  forall c1 c2:C,
    c1|>mapoid_c f g~c2|>mapoid_c f g ->
    c1~c2.
Proof.
  intros. simpl in H0. dependent induction H0.
  -  assumption.
  -  apply refl.
     - 

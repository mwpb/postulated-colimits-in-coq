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

Section Coequaliser.

  Variables R X:objoid.
  Variables s t:mapoid R X.

  Structure coequaliser:Type:=
    {coeq_obj:objoid;
     coeq_arr:mapoid X coeq_obj;
     cofork:
       s||>coeq_arr = t||> coeq_arr;
     coeq_induced:
       forall Z:objoid, forall z:mapoid X Z,
           forall (H:s||>z = t||>z),
           mapoid coeq_obj Z;
     coeq_fact:
       forall Z:objoid, forall z:mapoid X Z,
           forall (H:s||>z = t||>z),
           coeq_arr ||> coeq_induced Z z H = z;
     coeq_unique:
       forall Z:objoid, forall y z:mapoid coeq_obj Z,
           coeq_arr ||> y = coeq_arr ||> z ->
           y=z}.
  
  Inductive span(x1 x2:X):=
  |xid(H:x1~x2):span x1 x2
  |st(r:R) (H:x1~(s(r))) (H2:x2~(t(r))): span x1 x2
  |ts(r:R) (H:x2~(s(r))) (H2:x1~(t(r))): span x1 x2.

  Definition span_rev{x1 x2:X}(s1:span x1 x2):span x2 x1:=
    match s1 with
    |xid _ _ H=>xid x2 x1 (sym H)
    |st _ _ r H H2=>ts _ _ r H H2
    |ts _ _ r H H2=>st _ _ r H H2
    end.

  Inductive zigzag(x1 x2:X):Prop:=
  |zspan(s1:span x1 x2):zigzag x1 x2
  |zcons(x3:X)(s1:span x1 x3)(z1:zigzag x3 x2): zigzag x1 x2.

  Arguments zspan {x1}{x2}.
  Arguments zcons {x1}{x2}.
  Fixpoint zigzag_append {x1 x2 x3:X} (z1:zigzag x1 x2) (z2:zigzag x2 x3): zigzag x1 x3:=
    match z1 with
    |zspan s1=>zcons _ s1 z2
    |zcons _ s1 t=>zcons _ s1 (zigzag_append t z2)
    end.

  Fixpoint zigzag_rev {x1 x2:X}(z1:zigzag x1 x2):zigzag x2 x1:=
    match z1 with
    |zspan s1=> zspan (span_rev s1)
    |zcons _ s1 t=>zigzag_append (zigzag_rev t) (zspan (span_rev s1))
    end.

  Lemma zigzag_refl:
    forall x:X,
      zigzag x x.
  Proof.
    intro. apply zspan. apply xid. reflexivity. Qed.

  Lemma zigzag_sym:
    forall x1 x2:X,
      zigzag x1 x2 ->
      zigzag x2 x1.
  Proof.
    intros. apply zigzag_rev. assumption. Qed.

  Lemma zigzag_trans:
    forall x1 x2 x3:X,
      zigzag x1 x2 -> zigzag x2 x3 ->
      zigzag x1 x3.
  Proof.
    intros x1 x2 x3. apply zigzag_append. Qed.

  Definition Q:objoid:=
    {|carrier:=X;
      eq:=zigzag;
      refl:=zigzag_refl;
      sym:=zigzag_sym;
      trans:=zigzag_trans|}.

  Lemma id_pres:
    forall x1 x2:X,
      x1~x2->
      (fun x:X=>x:Q)(x1) ~ (fun x=>x)(x2).
  Proof.
    intros. simpl. apply zspan. apply xid. assumption. Qed.
  Definition q:mapoid X Q:=
    {|map:=fun x:X => x:Q;
      pres:=id_pres|}.

  Definition fact_arrow(Z:objoid) (z:mapoid X Z):Q->Z:=
    fun x:Q => z(x).

  Check mapoid_ext.
  Lemma fact_arrow_pres(Z:objoid) (z:mapoid X Z) (H:s||>z = t||>z):
    forall q1 q2:Q,
      q1~q2->
      fact_arrow Z z q1~fact_arrow Z z q2.
  Proof.
    intros. induction H0.
    - induction s1.
      -- unfold fact_arrow. apply pres. assumption.
      -- unfold fact_arrow. apply sym in H2. rewrite H0.
         rewrite <- H2. apply mapoid_app with r in H.
         simpl in H. assumption.
      -- unfold fact_arrow. apply sym in H2. rewrite H0.
         rewrite <- H2. apply mapoid_app with r in H.
         simpl in H. apply sym in H. assumption.
    - unfold fact_arrow in IHzigzag. unfold fact_arrow.
      induction s1.
      -- rewrite H1. assumption.
      -- apply mapoid_app with r in H. simpl in H.
         rewrite H1. rewrite H. rewrite <- H2. assumption.
      -- apply mapoid_app with r in H. simpl in H.
         rewrite H2. rewrite <- H. rewrite <- H1. assumption.
  Qed.     
    
  Definition factorisation (Z:objoid) (z:mapoid X Z) (H:s||>z = t||>z):mapoid Q Z:=
    {|map:=fact_arrow Z z;
      pres:=(fact_arrow_pres Z z H)|}.
  
  Lemma prf_coeq_fact:
    forall (Z:objoid) (z:mapoid X Z) (H:s||>z = t||>z),
      q ||> (factorisation Z z H) = z.
  Proof.
    intros. apply mapoid_ext. simpl. unfold fact_arrow. intro.
    apply refl. Qed.

  Lemma prf_coeq_unique:
    forall Z:objoid, forall y z:mapoid Q Z,
        q ||> y = q ||> z ->
        y=z.
  Proof.
    intros. apply mapoid_ext. intro.
    apply mapoid_app with a in H. simpl in H. assumption. Qed.

  Lemma coforks:
    s||>q = t||> q.
  Proof.
    apply mapoid_ext. simpl. intro. apply zspan. apply st with a.
    - apply refl.
    - apply refl. Qed.

  Definition mk_coequaliser:coequaliser:=
    {|coeq_obj:=Q;
      coeq_arr:=q;
      cofork:=coforks;
      coeq_induced:=factorisation;
      coeq_fact:=prf_coeq_fact;
      coeq_unique:=prf_coeq_unique|}.  
  
End Coequaliser.

Arguments coeq_obj{R}{X}{s}{t}.
Arguments coeq_arr{R}{X}{s}{t}.
Arguments cofork{R}{X}{s}{t}.
Arguments coeq_induced{R}{X}{s}{t}.
Arguments coeq_fact{R}{X}{s}{t}.
Arguments coeq_unique{R}{X}{s}{t}.

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
         ((u0||>(du_induced Z h k)) = h)
           /\(u1||>(du_induced Z h k)=k);
     du_unique:
       forall (Z:objoid) (x y:mapoid du_obj Z),
         (u0||>x=u0||>y)/\(u1||>x=u1||>y)->
         x=y}.
  
  Inductive du:Type :=
  |b:B -> du
  |c:C -> du.
  Inductive du_eq:relation du:=
  |beq(b1 b2:B) (H:b1~b2):du_eq (b b1) (b b2)
  |ceq(c1 c2:C) (H:c1~c2):du_eq (c c1) (c c2).
  (* |du_trans(x1 x2 x3:du) (H1:du_eq x1 x2) (H2:du_eq x2 x3): *)
  (*    du_eq x1 x3. *)
                                      
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

  Lemma b_pres:
    forall b1 b2:B,
      b1~b2 ->
      (b(b1):(carrier du_objoid)) ~ (b(b2):(carrier du_objoid)).
    Proof.
    intros. simpl. apply beq. assumption. Qed.

  Definition mapoid_b: mapoid B du_objoid :=
    {|map:= fun (b1:B)=>b(b1):(carrier du_objoid);
      pres:= b_pres|}.
  
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
      ((mapoid_b||>(du_factorisation Z h k)) = h)
      /\(mapoid_c||>(du_factorisation Z h k)=k).
  Proof.
    intros. split.
    - apply mapoid_ext. intros. simpl. apply refl.
    - apply mapoid_ext. intros. simpl. apply refl. Qed.
  
  Lemma prf_du_unique:
    forall (Z:objoid) (x y:mapoid du_objoid Z),
      (mapoid_b||>x=mapoid_b||>y)/\(mapoid_c||>x=mapoid_c||>y)->
      x=y.
  Proof.
    intros. apply mapoid_ext. intros. destruct H as (H0&H1).
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

Section pushout.

  Variables A B C:objoid.
  Variable f:mapoid A B.
  Variable g:mapoid A C.

  Structure Pushout:Type :=
    {pushout_obj:objoid;
     i0:mapoid B pushout_obj;
     i1:mapoid C pushout_obj;
     commutes: f||>i0 = g||>i1;
     po_induced:
       forall (Z:objoid) (h:mapoid B Z) (k:mapoid C Z)
              (H:f ||> h = g ||> k),
         mapoid pushout_obj Z;
     po_fact:
       forall (Z:objoid) (h:mapoid B Z) (k:mapoid C Z)
              (H:f ||> h = g ||> k),
         (i0||>(po_induced Z h k H)=h)/\
         (i1||>(po_induced Z h k H)=k);
     po_unique:
       forall (Z:objoid) (x y:mapoid pushout_obj Z),
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
    - apply mapoid_app with c0 in H0. simpl in H0. assumption.
    - apply mapoid_app with c0 in H1. simpl in H1. assumption.
  Qed.
    
  Definition mk_pushout:=
    {|pushout_obj:=(coeq_obj coeq);
      i0:=u0 BuC||>(coeq_arr coeq);
      i1:=u1 BuC||>(coeq_arr coeq);
      commutes:=prf_commutes;
      po_induced:=prf_po_induced;
      po_fact:=prf_po_fact;
      po_unique:=prf_po_unique|}.
    
        
        (* Definition s_map:A->carrier du_objoid:= *)
    (*   fun a=>b(f(a)). *)
    (* Lemma s_map_pres: *)
    (*   forall a1 a2:A, *)
    (*     a1~a2-> *)
    (*     s_map(a1)~s_map(a2). *)
    (* Proof. *)
    (*   intros. unfold s_map. apply beq. apply pres. assumption. *)
    (* Qed. *)
    (* Definition s_mapoid:= *)
    (*   {|map:=s_map; *)
    (*     pres:=s_map_pres|}. *)

    (* Definition t_map:A->carrier du_objoid:= *)
    (*   fun a=>c(g(a)). *)
    (* Lemma t_map_pres: *)
    (*   forall a1 a2:A, *)
    (*     a1~a2-> *)
    (*     t_map(a1)~t_map(a2). *)
    (* Proof. *)
    (*   intros. unfold t_map. apply ceq. apply pres. assumption. *)
    (* Qed. *)
    (* Definition t_mapoid:= *)
    (*   {|map:=t_map; *)
    (*     pres:=t_map_pres|}. *)

  (* Inductive blist:B->DisjointUnion->Type:= *)
  (* |singleB (b1:B):blist b1 (b b1) *)
  (* |consB (c1:C) (x1:DisjointUnion) (m:clist c1 x1) (a1:A) (H2:g(a1)=c1):blist (f(a1)) x1 *)
  (* with clist:C->DisjointUnion->Type:= *)
  (* |singleC (c1:C):clist c1 (c c1) *)
  (* |consC (b1:B) (x1:DisjointUnion) (a1:A) (H:f(a1)=b1):clist (g(a1)) x1. *)

  Record PType:Type:=
    {car:>Type;
     pt:car}.

  Definition cInC(c1:C):=
    {|car:=C;
      pt:=c1|}.
  Definition bInB(b1:B):=
    {|car:=B;
      pt:=b1|}.

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

  Definition spanBB(b1:B):=
    {x:span (bInB b1) (bInB b1)| x = refl_span (bInB b1)}.
  Definition spanCC(c1:C):=
    {x:span (cInC c1) (cInC c1)| x = refl_span (cInC c1)}.
  Definition spanBC(a1:A):=
    {x:span (bInB (f a1)) (cInC (g a1))| }
  
  Inductive zigzag:relation DisjointUnion:=
  |bnil(b1:B):zigzag (b b1) (b b1)
  |cnil(c1:C):zigzag (c c1) (c c1)
  |bunit(b1:B)(x3:DisjointUnion):bnil b1->zigzag (b b1) x3->zigzag (b b1) x3.

  Definition zigzag_app{x1 x2 x3:DisjointUnion}():
  
  
  
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

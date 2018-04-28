Require Import objoid_mapoid.
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
       s||>coeq_arr ~ t||> coeq_arr;
     coeq_induced:
       forall Z:objoid, forall z:mapoid X Z,
           forall (H:s||>z ~ t||>z),
           mapoid coeq_obj Z;
     coeq_fact:
       forall Z:objoid, forall z:mapoid X Z,
           forall (H:s||>z ~ t||>z),
           coeq_arr ||> coeq_induced Z z H ~ z;
     coeq_unique:
       forall Z:objoid, forall y z:mapoid coeq_obj Z,
           coeq_arr ||> y ~ coeq_arr ||> z ->
           y~z}.

  Inductive zigzag(x1 x2:X):Prop:=
  |xid (H:x1~x2):zigzag x1 x2
  |xcons {x3:X}: (x1~x3)-> (zigzag x3 x2) -> zigzag x1 x2
  |stcons{r:R}{x3:X} (H1:x1~(s(r))) (H2:x3~(t(r)))
         (z1:zigzag x3 x2): zigzag x1 x2
  |tscons{r:R}{x3:X} (H1:x1~(t(r))) (H2:x3~(s(r)))
         (z1:zigzag x3 x2): zigzag x1 x2.
        
  Arguments xid{x1}{x2}.
  Arguments xcons{x1}{x2}{x3}.
  Arguments stcons{x1}{x2}.
  Arguments tscons{x1}{x2}.
  
  Fixpoint zigzag_append {x1 x2 x3:X} (z1:zigzag x1 x2) (z2:zigzag x2 x3): zigzag x1 x3:=
    match z1 with
    |xid H=>xcons H z2
    |xcons H t=>xcons H (zigzag_append t z2)
    |stcons _ _ H1 H2 t=>stcons _ _ H1 H2 (zigzag_append t z2)
    |tscons _ _ H1 H2 t=>tscons _ _ H1 H2 (zigzag_append t z2)
    end.

  Fixpoint zigzag_rev {x1 x2:X}(z1:zigzag x1 x2):zigzag x2 x1:=
    match z1 with
    |xid H=>xid (sym H)
    |xcons H t=>zigzag_append (zigzag_rev t) (xid (sym H))
    |stcons _ _ H1 H2 t=>
     zigzag_append (zigzag_rev t) (tscons _ _ H2 H1 (xid (refl)))
    |tscons _ _ H1 H2 t=>
     zigzag_append (zigzag_rev t) (stcons _ _ H2 H1 (xid (refl)))
    end.

  Lemma zigzag_refl:
    forall x:X,
      zigzag x x.
  Proof.
    intros. apply xid. apply refl. Qed.

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
    intros. simpl. apply xid. assumption. Qed.

  Definition q:mapoid X Q:=
    {|map:=fun x:X => x:Q;
      pres:=id_pres|}.

  Definition fact_arrow(Z:objoid) (z:mapoid X Z):Q->Z:=
    fun x:Q => z(x).
  
  Lemma fact_arrow_pres(Z:objoid) (z:mapoid X Z) (H:s||>z ~ t||>z):
    forall q1 q2:Q,
      q1~q2->
      fact_arrow Z z q1~fact_arrow Z z q2.
  Proof.
    intros. induction H0.
    - unfold fact_arrow. apply pres. assumption.
    - unfold fact_arrow. unfold fact_arrow in IHzigzag.
      apply pres with z x1 x3 in H0. rewrite H0. assumption.
    - apply mapoid_app with r in H. simpl in H.
      unfold fact_arrow in IHzigzag. unfold fact_arrow.
      apply pres with z x1 (s r) in H1.
      apply pres with z x3 (t r) in H2. rewrite H in H1.
      rewrite H1. rewrite <- H2. assumption.
    - apply mapoid_app with r in H. simpl in H.
      unfold fact_arrow in IHzigzag. unfold fact_arrow.
      apply pres with z x1 (t r) in H1.
      apply pres with z x3 (s r) in H2. rewrite <- H in H1.
      rewrite H1. rewrite <- H2. assumption. Qed.
    
  Definition factorisation (Z:objoid) (z:mapoid X Z) (H:s||>z ~ t||>z):mapoid Q Z:=
    {|map:=fact_arrow Z z;
      pres:=(fact_arrow_pres Z z H)|}.
  
  Lemma prf_coeq_fact:
    forall (Z:objoid) (z:mapoid X Z) (H:s||>z ~ t||>z),
      q ||> (factorisation Z z H) ~ z.
  Proof.
    intros. simpl. unfold fact_arrow. intro.
    apply refl. Qed.

  Lemma prf_coeq_unique:
    forall Z:objoid, forall y z:mapoid Q Z,
        q ||> y ~ q ||> z ->
        y~z.
  Proof.
    simpl. unfold mapd_eq. intros. simpl in H. apply H. Qed.

  Lemma coforks:
    s||>q ~ t||> q.
  Proof.
    simpl. intro. apply stcons with a (t a).
    - apply refl.
    - apply refl.
    - apply xid. apply refl. Qed.
  
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
Arguments zigzag{R}{X}{s}{t}.
Arguments xcons{R}{X}{s}{t}.
Arguments xid{R}{X}{s}{t}.

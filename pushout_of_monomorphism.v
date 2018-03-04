Require Import objoid_mapoid.
Require Import pushout.
Require Import coequaliser.
Require Import disjoint_union.
Require Import Coq.Program.Equality.

Section TestPushout.
  
Variables A B C D:objoid.
Variable f:mapoid A B.
Variable g:mapoid A C.
Variable H:
  forall a1 a2:A,
    a1|>f~a2|>f ->
    a1~a2.

Definition P := mk_pushout f g.

Lemma f_mono_inner(x1 x2:po_obj P):
    x1~x2 ->
    match x1,x2 with
    |(c c1),(c c2)=>c1~c2
    |(b b1),(c c2)=>exists a:A, (f(a)~(b1))/\
                                (g(a)~c2)
    |_,_ => True
    end.
Proof.
  intros. induction H0.
  - induction x1, x2.
    -- trivial.
    -- inversion H0.
    -- trivial.
    -- inversion H0. assumption.
  - induction x1, x2.
    -- trivial.
    -- induction x3.
       --- destruct IHzigzag. destruct H2. exists x.
           split.
           ---- rewrite H2. apply sym. inversion H0. assumption.
           ---- assumption.
       --- inversion H0.
    -- trivial.
    -- induction x3.
       --- inversion H0.
       --- inversion H0. rewrite H4. assumption.
  - induction H0.
    -- induction x0,x1,x2.
       --- trivial.
       --- inversion H2.
       --- trivial.
       --- inversion H2.
       --- trivial.
       --- exists r. split.
           ---- simpl in H1. dependent induction H1.
                apply sym. assumption.
           ---- rewrite H0 in H2. inversion H2. apply sym.
                assumption.
       --- trivial.
       --- inversion H1.
    -- induction x0,x1,x2,x3.
       --- trivial.
       --- trivial.
       --- inversion H2.
       --- inversion H2.
       --- inversion H1.
       --- inversion H1.
       --- inversion H1.
       --- inversion H2.
       --- inversion H0.
       --- trivial.
       --- inversion H0.
       --- rewrite H0 in H2. apply IHzigzag0.
           ---- assumption.
           ---- inversion H0. rewrite <- IHzigzag.
                apply sym. assumption.
       --- trivial.
       --- trivial.
       ---inversion H1.
       --- inversion H1.
    -- induction x0,x1,x2,x3.
       --- trivial.
       --- trivial.
       --- inversion H2.
       --- inversion H2.
       --- trivial.
       --- inversion H2.
       --- inversion H1.
       --- inversion H2.
       --- inversion H0.
       ---inversion H0.
       --- inversion H0.
       ---inversion H0.
       --- trivial.
       --- inversion H1.
       --- inversion H1.
       --- inversion H1.
    -- induction x0,x1,x2,x3.
       --- trivial.
       --- trivial.
       --- inversion H2.
       --- inversion H2.
       --- trivial.
       --- inversion H2.
       --- inversion H1.
       --- inversion H2.
       --- trivial.
       --- trivial.
       --- exists r. split.
           ---- inversion H1. apply sym. assumption.
           ---- rewrite <- IHzigzag. inversion H2. apply sym.
                assumption.
       --- inversion H3.
       --- trivial.
       --- trivial.
       --- inversion H1.
       --- inversion H1.
  - induction H0.
    -- induction x0,x1,x2.
       --- trivial.
       --- inversion H1.
       --- trivial.
       --- inversion H0.
       --- trivial.
       --- inversion H1.
       --- inversion H2.
       --- inversion H2.
    -- induction x0,x1,x2,x3.
       --- trivial.
       --- trivial.
       --- inversion H1.
       --- inversion H1.
       --- trivial.
       --- trivial.
       --- rewrite H0 in H2. apply IHzigzag0.
           ---- assumption.
           ---- destruct IHzigzag. destruct H4. exists x. split.
                ----- inversion H0. rewrite <- H8. assumption.
                ----- assumption.
       --- inversion H0.
       --- trivial.
       --- trivial.
       --- inversion H1.
       --- inversion H1.
       --- trivial.
       --- trivial.
       --- inversion H2.
       --- inversion H2.
    -- induction x0,x1,x2,x3.
       --- trivial.
       --- trivial.
       --- inversion H1.
       --- inversion H1.
       --- inversion H3.
       --- trivial.
       --- inversion H3.
       --- destruct IHzigzag. destruct H5. assert (sim:r~x).
           ---- inversion H2. rewrite H9 in H5. apply H. rewrite H5.
                apply refl.
           ---- rewrite <- sim in H6. rewrite <- H6. inversion H1.
                assumption.
       --- trivial.
       --- trivial.
       --- inversion H3.
       --- inversion H0.
       --- trivial.
       --- trivial.
       --- inversion H2.
       --- inversion H2.
    -- rewrite H0 in H2. inversion H2.
Qed.

Lemma po_of_mono:
  forall c1 c2:C,
    c1|>i1 P~c2|>i1 P ->
    c1~c2.
Proof.
  intros. apply f_mono_inner with (x1:=(c c1)) (x2:=(c c2)). assumption.
  Qed.
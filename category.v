Require Import objoid_mapoid.
Require Import Morphisms.
Section category.

  Record category :=
    {obj:objoid;
     arr:>objoid;
     s:mapoid arr obj;
     t:mapoid arr obj;
     e:mapoid obj arr;
     section_s: forall x:obj, s(e(x))~x;
     section_t: forall x:obj, t(e(x))~x;
     comp: forall f g:arr, t(f)~s(g) -> arr;
     comp_s {f g:arr}: forall (H:t(f)~s(g)), s(comp f g H)~s(f);
     comp_t {f g:arr}: forall (H:t(f)~s(g)), t(comp f g H)~t(g);
     left_id:
       forall (f:arr),
         comp (e(s(f))) f (section_t (s(f)))~f;
     right_id:
       forall (f:arr),
         comp f (e(t(f))) (sym (section_s (t(f))))~f;
     assoc:
       forall (f g h:arr) (H:t(f)~s(g)) (K:t g~s h),
         comp f (comp g h K) (trans H (sym(comp_s K)))~
              comp (comp f g H) h (trans (comp_t H) K)}.
  Arguments s{c}.
  Arguments t{c}.
  Arguments e{c}.

  Record functor (A B:category):=
    {arr_map:>mapoid A B;
     obj_map:mapoid (obj A) (obj B);
     e_pres:e||>arr_map = obj_map ||> e;
     s_pres: arr_map||>s = s||>obj_map;
     t_pres: arr_map||>t = t||>obj_map}.  
  
End category.

Arguments s{c}.
Arguments t{c}.
Arguments e{c}.
Arguments section_s{c}.
Arguments section_t{c}.
Arguments comp{c}.
Arguments comp_s{c}{f}{g}.
Arguments comp_t{c}{f}{g}.
Arguments left_id{c}.
Arguments right_id{c}.
Arguments assoc{c}.
Arguments arr_map{A}{B}.
Arguments obj_map{A}{B}.
Arguments e_pres{A}{B}.
Arguments s_pres{A}{B}.
Arguments t_pres{A}{B}.

Section words.

  Require Import pushout.
  Require Import disjoint_union.
  Require Import coequaliser.
  
  Variables A B C:category.
  Variable F:functor A B.
  Variable G:functor A C.

  Definition Q0 := mk_pushout (obj_map F) (obj_map G).
  Definition Q1:= mk_pushout F G.

  Lemma s_types:
    (F||>s||>i0 Q0) ~ G||>s||>i1 Q0.
  Proof.
    rewrite compn_assoc. rewrite compn_assoc.
    rewrite (s_pres F). rewrite (s_pres G).
    rewrite <- compn_assoc. rewrite <- compn_assoc.
    rewrite commutes. reflexivity. Qed.
  
  Lemma t_types:
    (F||>t||>i0 Q0) ~ G||>t||>i1 Q0.
   Proof.
    rewrite compn_assoc. rewrite compn_assoc.
    rewrite (t_pres F). rewrite (t_pres G).
    rewrite <- compn_assoc. rewrite <- compn_assoc.
    rewrite commutes. reflexivity. Qed.

  Lemma e_types:
    (obj_map F||>e||>i0 Q1)~(obj_map G||>e||>i1 Q1).
  Proof.
    rewrite compn_assoc. rewrite compn_assoc.
    rewrite <- e_pres. rewrite <- e_pres.
    rewrite <- compn_assoc. rewrite <- compn_assoc.
    rewrite commutes. reflexivity. Qed.
  
  Definition s_Q:mapoid (po_obj Q1) (po_obj Q0):=
    po_induced Q1 (po_obj Q0) (s||>i0 Q0) (s||>i1 Q0) s_types.
  Definition t_Q:mapoid (po_obj Q1) (po_obj Q0):=
    po_induced Q1 (po_obj Q0) (t||>i0 Q0) (t||>i1 Q0) t_types.
  Definition e_Q:mapoid (po_obj Q0) (po_obj Q1):=
    po_induced Q0 (po_obj Q1) (e||>i0 Q1) (e||>i1 Q1) e_types.

  Inductive Ph:(po_obj Q0)->(po_obj Q0)->Type:=
  |qin (q0:po_obj Q1):Ph (s_Q q0) (t_Q q0)
  |compose {x0 x1 x2: po_obj Q0} (p0:Ph x0 x1) (p1:Ph x1 x2):Ph x0 x2.
  
  Inductive P:Type:=
  |pin {x0 x1:po_obj Q0} (ph:Ph x0 x1):P.

  Definition P_eq(p0 p1:P):Prop:=
    match p0,p1 with
    |pin (Ph x0 x1), pin (Ph x3 x4) =>
     match (Ph x0 x1) with
     |qin q0=>
     |compose p0 p1=>
    
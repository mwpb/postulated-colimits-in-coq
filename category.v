Require Import objoid_mapoid.

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
     id_pres:e||>arr_map = obj_map ||> e;
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
Arguments id_pres{A}{B}.
Arguments s_pres{A}{B}.
Arguments t_pres{A}{B}.

Section words.

  Require Import pushout.
  
  Variables A B C:category.
  Variable F:functor A B.
  Variable G:functor A C.

  Definition words_obj_pushout:=
    mk_pushout (obj_map F) (obj_map G).

  Definition Q0:objoid:= po_obj words_obj_pushout.

  Inductive words_arr: Q0 -> Q0 -> Type:=
  |id (x0:Q0): words_arr x0 x0
  |b_arr (b1:B) (x0:Q0):
     (words_arr x0 (i0 words_obj_pushout (s b1))) -> (words_arr x0 (i0 words_obj_pushout (t b1)))
  |c_arr (c1:C) (x0:Q0):
     (words_arr x0 (i1 words_obj_pushout (s c1))) -> (words_arr x0 (i1 words_obj_pushout (t c1))).

  
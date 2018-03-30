Require Import objoid_mapoid.

Section category.

  Record deductive_system :=
    {obj:objoid;
     arr:objoid;
     s:mapoid arr obj;
     t:mapoid arr obj;
     e:mapoid obj arr;
     section_s: forall x:obj, s(e(x))~x;
     section_t: forall x:obj, t(e(x))~x;
     comp: forall f g:arr, t(f)~s(g) -> arr;
     comp_s: forall (f g:arr) (H:t(f)~s(g)), s(comp f g H)~s(f);
     comp_t: forall (f g:arr) (H:t(f)~s(g)), t(comp f g H)~t(g)}.
  (* What about a simplicial approach? *)

  Arguments s{d}.
  Arguments t{d}.
  Arguments e{d}.
  Arguments section_s{d}.
  Arguments section_t{d}.
  Arguments comp{d}.
  Arguments comp_s{d}{f}{g}.
  Arguments comp_t{d}{f}{g}.
  
  Record category :=
    {ded:deductive_system;
     left_id:
       forall (f:arr ded),
         comp (e(s(f))) f (section_t (s(f)))~f;
     right_id:
       forall (f:arr ded),
         comp f (e(t(f))) (sym (section_s (t(f))))~f;
     assoc:
       forall (f g h:arr ded) (H:t(f)~s(g)) (K:t g~s h),
         comp f (comp g h K) (trans H (sym(comp_s K)))~
              comp (comp f g H) h (trans (comp_t H) K)
    }.
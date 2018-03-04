(* category from Lean project *)

(* namespace category

open objoid

structure deductive_system :=
    (obj:objoid)
    (arr:objoid)
    (s: mapoid arr obj)
    (t: mapoid arr obj)
    (e: mapoid obj arr)
    (section_s: ∀ x:obj.carrier, x |> e |> s ∼ x)
    (section_t: ∀ x:obj.carrier, x |> e |> t ∼ x)
    (comp: ∀ f g:arr.carrier, f |> t ∼ g |> s → arr.carrier)
    (comp_s: Π f g:arr.carrier, Π (H: f |> t ∼ g |> s), (comp f g H) |> s ∼ f |> s)
    (comp_t: Π f g:arr.carrier, Π (H: f |> t ∼ g |> s), (comp f g H) |> t ∼ g |> t)

lemma left_id_type (D:deductive_system) (f:D.arr.carrier): f |> D.s |> D.e |> D.t ∼ f |> D.s :=
begin
    apply D.section_t
end

lemma right_id_type (D:deductive_system) (f:D.arr.carrier): f |> D.t = f |> D.t |> D.e |> D.s := 
begin
    symmetry,
    apply D.section_s
end

lemma assoc_type_1 (D:deductive_system) (f g h: D.arr) (H1:D.t(f)=D.s(g)) (H2:D.t(g)=D.s(h)): D.t(D.comp f g H1) = D.s(h) :=
begin
    rewrite D.comp_t,
    apply H2
end

lemma assoc_type_2 (D:deductive_system) (f g h:D.arr) (H1:D.t(f)=D.s(g)) (H2:D.t(g)=D.s(h)): D.t(f) = D.s(D.comp g h H2)  :=
begin
    rewrite D.comp_s g h H2,
    apply H1
end

structure category :=
    (ded:deductive_system)
    (left_id: Π (f:ded.arr), (ded.comp (ded.e(ded.s(f))) f (left_id_type ded f)) = f)
    (right_id: Π (f:ded.arr), (ded.comp f (ded.e(ded.t(f))) (right_id_type ded f)) = f)
    (assoc: Π (f g h:ded.arr), Π (H1:ded.t(f)=ded.s(g)), Π (H2:ded.t(g)=ded.s(h)),
        ded.comp (ded.comp f g H1) h (assoc_type_1 ded f g h H1 H2) = ded.comp f (ded.comp g h H2) (assoc_type_2 ded f g h H1 H2))

end category *)
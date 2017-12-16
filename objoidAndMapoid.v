Section objoid.

Structure objoid:Type :={
carrier:Type;
eq:carrier->carrier->Prop;
eq_refl (x:carrier): eq x x;
eq_sym (x y:carrier) (H:eq x y): eq y x;
eq_trans (x y z:carrier) (H1:eq x y) (H2:eq y z): eq x z
}.

Arguments eq {o}.
Arguments eq_refl {o} {x}.
Arguments eq_sym {o} {x} {y}.
Arguments eq_trans {o} {x} {y} {z}.
Infix "~" := eq (at level 80, right associativity).

Structure mapoid (a b:objoid) := {
map:carrier a-> carrier b;
pres (a1 a2:carrier a) (H:a1~a2): map a1~map a2
}.

Arguments map {a} {b}.
Arguments pres {a} {b}.

Definition apply (a b:objoid) (a1:carrier a) (f:mapoid a b) := map f a1.

Arguments apply {a} {b}.
Infix "|>" := apply (at level 71, left associativity).

End objoid.
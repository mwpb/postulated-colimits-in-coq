Section objoid.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Structure objoid := {
    carrier:>Type;
    eq: Setoid carrier
}.

Structure mapoid (A B: objoid) := {
    map:> A -> B;
    pres (a1 a2:A) (H:a1=a2): map a1=map a2
}.

Arguments map {A} {B}.
Arguments pres {A} {B}.

Definition apply (A B: objoid) (a1:A) (f:mapoid A B) := map f a1.

Arguments apply {A} {B}.
Infix "|>" := apply (at level 11, left associativity).

End objoid.

Arguments map {A} {B}.
Arguments pres {A} {B}.

Arguments apply {A} {B}.

Infix "|>" := apply (at level 11, left associativity).
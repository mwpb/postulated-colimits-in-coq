Section objoid.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

(*  an objoid is like a setoid but we don't have to carry around
    the Type of the carrier *)
Structure objoid := {
    carrier:>Type;
    eq: Setoid carrier
}.

(*  a mapoid is a function between the carriers of two objoids
    that preserves the equivalence *)
Structure mapoid (A B: objoid) := {
    map:> A -> B;
    pres (a1 a2:A) (H:a1=a2): map a1=map a2
}.

Arguments map {A} {B}.

Definition apply (A B: objoid) (a1:A) (f:mapoid A B) := map f a1.

End objoid.

Arguments map {A} {B}.
Arguments pres {A} {B}.

Arguments apply {A} {B}.

Infix "|>" := apply (at level 11, left associativity).
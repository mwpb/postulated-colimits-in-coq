Section objoid.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Structure mapoid (A B:Type) (a:Setoid A) (b: Setoid B) := {
map:> A->B;
pres (a1 a2:A) (H:a1=a2): map a1=map a2
}.

Arguments mapoid {A}{B}.
Arguments map {A} {B} {a}{b}.
Arguments pres {A} {B}.

Definition apply (A B:Type) (a:Setoid A) (b:Setoid B) (a1:A) (f:mapoid a b) := map f a1.

Arguments apply {A} {B} {a}{b}.
Infix "|>" := apply (at level 11, left associativity).

End objoid.

Arguments mapoid {A}{B}.
Arguments map {A} {B} {a}{b}.
Arguments pres {A} {B}.
Arguments apply {A} {B} {a}{b}.

Infix "~" := eq (at level 20, right associativity).
Infix "|>" := apply (at level 11, left associativity).
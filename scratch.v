Require Import Coq.Program.Equality.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Section objArr.

Structure obj:Type:=
  {carrier:Type;
   rel:>relation carrier}.

Arguments rel{o}.

Infix "~" := rel (at level 101, left associativity).

Structure arr (A B:obj):=
  {map:carrier A->carrier B;
   pres (a1 a2:carrier A):(a1~a2)->(map(a1)~map(a2))}.

Arguments map{A}{B}.

End objArr.

Arguments rel{o}.
Infix "~" := rel (at level 101, left associativity).

Variable A:Type.
Variable relA:relation A.

Inductive EqA (a1 a2:A):Prop:=
|inc: relA a1 a2 -> EqA a1 a2
|sym:EqA a2 a1 -> EqA a1 a2.

Check EqA_ind.

Definition o:=
  {|carrier:=A;
    rel:=EqA|}.

Lemma tester: forall a1 a2:carrier o, (a2~a1) -> (a1~a2).
Proof.
  intros. simpl in H. dependent induction H.
  - 
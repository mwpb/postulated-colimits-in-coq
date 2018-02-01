Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Section objArr.

Structure obj:Type:=
  {carrier:Type;
   rel:relation carrier;
   ind (a1 a2:carrier):rel a1 a2 -> a1=a2}.

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

Inductive EqA:relation A:=
|inc(a1 a2:A): relA a1 a2 -> EqA a1 a2
|sym(a1 a2:A):EqA a1 a2 -> EqA a2 a1.

Definition o:=
  {|carrier:=A;
    rel:=EqA;
  ind:=|}.

Lemma tester: forall a1 a2:carrier o, a1~a2.
Proof.
  intros. induction (rel a1 a2).
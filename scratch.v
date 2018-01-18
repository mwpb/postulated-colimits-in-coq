Theorem unit_singleton : forall x : unit, x = tt.
Proof.
    intro.
    induction x.
    reflexivity.
Qed.

Compute bool_ind.

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
Proof.
    intros.
    induction b.
    unfold negb.
    reflexivity.

    unfold negb.
    reflexivity.
Qed.


Theorem n_plus_O : forall n : nat, plus n O = n.
Proof.
    intros.
    induction n.
    simpl.
    reflexivity.

    simpl.
    rewrite IHn.
    reflexivity.
Qed.
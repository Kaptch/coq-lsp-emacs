Import Nat.

Lemma test : 1 + 2 = 3.
Proof.
  reflexivity.
Qed.

Lemma test1 : forall (A : Type), A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A * A .
Proof.
  admit.
Admitted.

Check test.
Check test1.

Lemma test2 : forall n,
n > 0 ->
n + 1 = 1 + n.
Proof.
intros.
simpl.
set (n' := n+1).
set (n'' := n+1).
induction n.
- admit.
- admit.
Admitted.

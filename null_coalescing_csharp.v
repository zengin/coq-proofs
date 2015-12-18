(*** 
  Proof that null coalescing operator of C# is associative
  on simple value assignments. The operator is normally
  right associative. See:

  http://stackoverflow.com/questions/6238074/how-the-right-associative-of-null-coalescing-operator-behaves
***)

Variable A: Type.

Definition null_coalescing (x: option A) (y: option A) :=
match x with
| None => y
| _ => x
end.

Notation "x ?? y" := (null_coalescing x y) (at level 50).

Lemma assoc: forall x y z, x ?? (y ?? z) = (x ?? y) ?? z.

Proof.
intros.
induction x; simpl; reflexivity.
Qed.

Print assoc.
Require Import List.

Lemma list_max_map {X} (f g : X -> nat) (fg : forall x, f x <= g x)
  (xs : list X) : list_max (map f xs) <= list_max (map g xs).
Proof.
  induction xs; simpl.
  - constructor.
  - simpl.
    apply PeanoNat.Nat.max_le_compat.
    + apply fg.
    + exact IHxs.
Qed.

Lemma list_max_ne_achieves (xs : list nat) :
  {xs = nil} + {In (list_max xs) xs}.
Proof.
  induction xs.
  - now left.
  - right.
    simpl.
    destruct IHxs.
    + left.
      rewrite e.
      symmetry; apply PeanoNat.Nat.max_0_r.
    + destruct (PeanoNat.Nat.max_spec_le a (list_max xs))
        as [[_ Hle]|[_ Hle]];
      rewrite Hle; tauto.
Defined.

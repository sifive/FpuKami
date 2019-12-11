Require Import Psatz Kami.Lib.Word PeanoNat.

Definition lgCeil i := S (Nat.log2_iter (pred (pred i)) 0 1 0).

Lemma lgCeilGe1: forall x, lgCeil x >= 1.
Proof.
  unfold lgCeil.
  induction x; simpl; lia.
Qed.

Lemma lgCeil_log2: forall x, S (Nat.log2 (pred x)) = lgCeil x.
Proof.
  intros; auto.
Qed.
  
Lemma pow2_lgCeil: forall x, Nat.pow 2 (lgCeil x) >= x.
Proof.
  setoid_rewrite <- lgCeil_log2.
  intros.
  destruct x; simpl; try lia.
  destruct x; simpl; try lia.
  pose proof (Nat.log2_spec (S x) ltac:(lia)) as [? ?].
  simpl in *.
  lia.
Qed.

Lemma pow2_pow2: forall x, Nat.pow 2 x + Nat.pow 2 x = Nat.pow 2 (S x).
Proof.
  induction x; simpl; try lia.
Qed.

Lemma pow2Ge1: forall x, Nat.pow 2 x >= 1.
Proof.
  induction x; simpl; lia.
Qed.

Lemma lgCeil_pow2: forall x, x > 0 -> x = lgCeil (Nat.pow 2 x).
Proof.
  setoid_rewrite <- lgCeil_log2.
  intros.
  destruct x; simpl; try lia.
  repeat setoid_rewrite <- plus_n_O.
  rewrite pow2_pow2.
  rewrite Nat.log2_pred_pow2; try lia.
Qed.

From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

(* swiped from an earlier version of SSReflect *)
Definition seq2matrix (T: ringType) m n (l: seq (seq T)) :=
  \matrix_(i<m,j<n) nth 1 (nth [::] l i) j.

Notation "''M{' l } " := (seq2matrix _ _ l).

Lemma sum_mul_dist: forall (T: ringType) m n (F: 'I_m -> T) (G: 'I_n -> T), 
  (\sum_(i < m) F i) * (\sum_(j < n) G j) =
  \sum_(i < m) F i * \sum_(j < n) G j.
Proof.
  intros. induction m;
  [ rewrite !big_ord0; apply mul0r
  | rewrite !big_ord_recl; rewrite mulrDl; rewrite IHm //
  ].
Qed.

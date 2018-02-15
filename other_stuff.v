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

Lemma sum_add_dist: forall (T: ringType) m (F: 'I_m -> T) (G: 'I_m -> T), 
  (\sum_(i < m) F i) + (\sum_(i < m) G i) =
  \sum_(i < m) (F i + G i).
Proof.
  intros. induction m;
  [ rewrite !big_ord0; apply add0r
  | rewrite !big_ord_recl
  ].
  rewrite (addrC (F ord0)). rewrite -(addrA _ (F ord0)). rewrite (addrA (F ord0)).
  rewrite (addrC (F ord0 + G ord0)). rewrite (addrA _ _ (F ord0 + G ord0)). rewrite addrC.
  rewrite IHm //.
Qed.

Lemma sum_mul_dist: forall (T: ringType) m n (F: 'I_m -> T) (G: 'I_n -> T), 
  (\sum_(i < m) F i) * (\sum_(j < n) G j) =
  \sum_(i < m) F i * \sum_(j < n) G j.
Proof.
  intros. induction m;
  [ rewrite !big_ord0; apply mul0r
  | rewrite !big_ord_recl; rewrite mulrDl; rewrite IHm //
  ].
Qed.

Lemma sum_cast: forall (R: zmodType) m n (Heq: m = n) (P1: pred 'I_m) (P2: pred 'I_n)
  (F1: 'I_m -> R) (F2: 'I_n -> R),
  (forall x, P1 x = P2 (cast_ord Heq x)) ->
  (forall x, F1 x = F2 (cast_ord Heq x)) ->
  \sum_(i < m | P1 i) F1 i =
  \sum_(i < n | P2 i) F2 i.
Proof.
  intros.
    replace (\sum_(i < m | P1 i) F1 i) with (\sum_(i < m) (if P1 i then F1 i else 0)).
    replace (\sum_(i < n | P2 i) F2 i) with (\sum_(i < n) (if P2 i then F2 i else 0)).
  generalize P1 P2 F1 F2 Heq H H0. clear P1 P2 F1 F2 H H0 Heq. generalize m n. clear m n.
  double induction m n.
    intros; rewrite !big_ord0 //.
    intros; inversion Heq.
    intros; inversion Heq.
    intros. clear H n0 m.
      rewrite !big_ord_recl. inversion Heq.
      rewrite (H0 n _ (fun x => P2 (fintype.lift ord0 x)) _ (fun x => F2 (fintype.lift ord0 x))).
      rewrite H1. rewrite H2. replace (F2 (cast_ord Heq ord0)) with (F2 ord0).
      replace (P2 (cast_ord Heq ord0)) with (P2 ord0). reflexivity.
      compute. rewrite (eq_irrelevance (ltn0Sn n) (cast_ord_proof (Ordinal (ltn0Sn n1)) Heq)). reflexivity.
      compute. rewrite (eq_irrelevance (ltn0Sn n) (cast_ord_proof (Ordinal (ltn0Sn n1)) Heq)). reflexivity.
    intros; rewrite H1. compute. rewrite (eq_irrelevance (@cast_ord_proof (S n1) (S n) (@Ordinal (S n1) _ (@lift_subproof (S n1) 0 x)) Heq)
       (@lift_subproof (S n) 0 (@Ordinal n _ (@cast_ord_proof n1 n x H3)))
     ). reflexivity.
    intros; rewrite H2. compute. rewrite (eq_irrelevance (@cast_ord_proof (S n1) (S n) (@Ordinal (S n1) _ (@lift_subproof (S n1) 0 x)) Heq)
       (@lift_subproof (S n) 0 (@Ordinal n _ (@cast_ord_proof n1 n x H3)))
     ). reflexivity.
   rewrite -big_mkcond. reflexivity. rewrite -big_mkcond. reflexivity.
Qed.

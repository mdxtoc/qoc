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

Lemma sum_cast: forall (R: ringType) m n (Heq: m = n) (P1: pred 'I_m) (P2: pred 'I_n)
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

Lemma sum_if_not: forall (R: ringType) m P (F: 'I_m -> R),
  \sum_(i < m | ~~P i) F i + \sum_(i < m | P i) F i = \sum_(i < m) F i.
Proof.
  intros. rewrite (big_mkcond (fun i => ~~P i)). rewrite (big_mkcond (fun i => P i)).
  rewrite sum_add_dist. induction m;
  [ rewrite !big_ord0 //
  | rewrite !big_ord_recl; destruct (P ord0); [ rewrite add0r | rewrite addr0 ]; rewrite IHm //
  ].
Qed.

Lemma behead_tupleE: forall T k h (l: k.-tuple T), behead_tuple ([tuple of h :: l]) = [tuple of l].
Proof.
  intros. apply eq_from_tnth. intro. 
    rewrite !(tnth_nth h). simpl.
    reflexivity. 
Qed.

Lemma ordinal_eq: forall m i j Hi Hj, i = j -> (@Ordinal m i Hi) = (@Ordinal m j Hj).
Proof.
  intros. generalize Hi. clear Hi. rewrite H. intros Hi. rewrite (eq_irrelevance Hi Hj) //.
Qed.

Lemma leq_lt: forall a b: nat, (a >= b)%N -> ~(b > a)%N.
Proof.
  intros. apply/elimF. Focus 2. rewrite leqNgt in H. apply negbTE. apply H.
    destruct (a < b)%N; [ apply ReflectT | apply ReflectF ]; auto.
Qed.
 
Lemma blerp: forall a b c d x, 
  (a * x + b = c * x + d -> b < x -> d < x -> a = c /\ b = d)%N.
Proof.
  intros. generalize a c H. clear a c H. double induction a c.
    split. reflexivity. rewrite !mul0n in H. rewrite !add0n in H. exact H.
    rewrite !mul0n. rewrite !add0n. intros.
      absurd (b < x)%N. rewrite H2. apply leq_lt. apply leq_trans with (n.+1 * x)%N.
        apply leq_pmull. auto. apply leq_addr.
        apply H0.
    rewrite !mul0n. rewrite !add0n. intros.
      absurd (d < x)%N. rewrite -H2. apply leq_lt. apply leq_trans with (n.+1 * x)%N.
        apply leq_pmull. auto. apply leq_addr.
        apply H1.
   intros. assert (n0 * x + b = n * x + d)%N.
     rewrite !mulSnr in H3. rewrite addnAC in H3. rewrite (addnAC (n*x)%N x d) in H3.
     apply/eqP. rewrite -(eqn_add2r x). apply/eqP. apply H3. split.
       f_equal. apply (proj1 (H2 n H4)).
       apply (proj2 (H2 n H4)).
Qed.

Lemma implP: forall A B,
  is_true (A ==> B) -> is_true A -> is_true B.
Proof.
  intros. destruct A. apply H.
  inversion H0.
Qed.

Lemma andP: forall A B,
  is_true (A && B) <-> is_true A /\ is_true B.
Proof.
  split.
    intros. destruct A. destruct B.
     auto.
     inversion H.
     inversion H.
    intros. destruct A. destruct B.
      auto.
      destruct H. inversion H0.
      destruct H. inversion H.
Qed.

Lemma modn: forall x y z,
 (0 < y)%N -> x %% (z * y) = x %[mod y]%N.
Proof.
  intros. rewrite !modn_def.
  case:edivnP. intros q r. case:edivnP. intros q' r'. case:edivnP. intros q'' r''. intros. simpl.
    simpl in e1. rewrite e1 in e0. clear e1. rewrite e in e0. clear e. rewrite mulnA in e0. rewrite addnA in e0.
    rewrite -mulnDl in e0. symmetry. apply (blerp e0).
    apply (implP i). apply H.
    apply (implP i1). apply H.
Qed.

Lemma mxtensA: forall (R: ringType) ma na mb nb mc nc (Hma: (0 < ma)%N) (Hna: (0 < na)%N) (Hmb: (0 < mb)%N)
  (Hnb: (0 < nb)%N) (Hmc: (0 < mc)%N) (Hnc: (0 < nc)%N) (a: 'M[R]_(ma, na)) (b: 'M[R]_(mb, nb)) (c: 'M[R]_(mc, nc)),
  castmx (mulnA ma mb mc, mulnA na nb nc) (a *t (b *t c)) = a *t b *t c.
Proof.
  intros; apply/matrixP; intros i j. rewrite castmxE. unfold cast_ord. unfold tensmx. rewrite !mxE. simpl. rewrite mulrA. f_equal. f_equal.
    rewrite (ordinal_eq (mxtens_index_proof1 (Ordinal (cast_ord_proof i (esym (mulnA ma mb mc))))) (mxtens_index_proof1 (Ordinal (mxtens_index_proof1 i)))).
    rewrite (ordinal_eq (mxtens_index_proof1 (Ordinal (cast_ord_proof j (esym (mulnA na nb nc))))) (mxtens_index_proof1 (Ordinal (mxtens_index_proof1 j)))).
      reflexivity. rewrite -divnMA. rewrite (mulnC nc nb). auto.
      rewrite -divnMA. rewrite (mulnC mc mb). auto.
    rewrite (ordinal_eq (mxtens_index_proof1 (Ordinal (mxtens_index_proof2 (Ordinal (cast_ord_proof i (esym (mulnA ma mb mc))))))) (mxtens_index_proof2 (Ordinal (mxtens_index_proof1 i)))).
    rewrite (ordinal_eq (mxtens_index_proof1 (Ordinal (mxtens_index_proof2 (Ordinal (cast_ord_proof j (esym (mulnA na nb nc))))))) (mxtens_index_proof2 (Ordinal (mxtens_index_proof1 j)))).
      reflexivity.
      simpl. rewrite !modn_def. case: edivnP =>  q r. case: edivnP => q' r'. simpl. intros. rewrite e0 in e. rewrite mulnA in e.
      rewrite divnMDl in e.
      apply (blerp e). rewrite ltn_divLR. apply (implP i1). rewrite muln_gt0. apply <- andP. split. apply Hnb. apply Hnc. apply Hnc.
      apply (implP i0). apply Hnb. apply Hnc.
      simpl.  rewrite !modn_def. case: edivnP =>  q r. case: edivnP => q' r'. simpl. intros. rewrite e0 in e. rewrite mulnA in e.
      rewrite divnMDl in e.
      apply (blerp e). rewrite ltn_divLR. apply (implP i1). rewrite muln_gt0. apply <- andP. split. apply Hmb. apply Hmc. apply Hmc.
      apply (implP i0). apply Hmb. apply Hmc.
    rewrite (ordinal_eq (mxtens_index_proof2 (Ordinal (mxtens_index_proof2 (Ordinal (cast_ord_proof i (esym (mulnA ma mb mc))))))) (mxtens_index_proof2 i)).
    rewrite (ordinal_eq (mxtens_index_proof2 (Ordinal (mxtens_index_proof2 (Ordinal (cast_ord_proof j (esym (mulnA na nb nc))))))) (mxtens_index_proof2 j)).
      reflexivity.
      simpl. apply modn. apply Hnc.
      simpl. apply modn. apply Hmc.
Qed.
 

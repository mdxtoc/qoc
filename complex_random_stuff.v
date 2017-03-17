From mathcomp Require Import all_ssreflect all_real_closed all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Parameter R: rcfType.

Local Open Scope ring_scope.

Definition conjugate m n (mx: 'M[R [i]]_(m, n)): 'M[R [i]]_(m, n) :=
  map_mx conjc mx.

Definition conjugate_transpose m n (mx: 'M[R [i]]_(m, n)) :=
  (conjugate mx)^T.

Definition unitarymx (n: nat) (mx: 'M[R [i]]_n) :=
  (conjugate_transpose mx) *m mx = 1%:M.

Lemma cond_add_blerp: forall (a b: R [i]),
  ((a^* + b^*) = (a + b)^*)%C.
Proof.
  intros a b. destruct a as [ar ai]. destruct b as [br bi]. simpc. rewrite -GRing.opprD. reflexivity.
Qed.

Lemma csum: forall I (F: I -> R [i]) (r: seq I) P,
  ((\sum_(i <- r | P) F i)^*%C) = \sum_(i <- r | P) (fun x => ((F x)^*)%C) i.
Proof.
  move => I F r P. induction r.
    rewrite !big_nil. apply conjc0.
    rewrite !big_cons. destruct P.
      rewrite -cond_add_blerp. rewrite IHr. reflexivity.
      apply IHr.
Qed.

Lemma cond_mul_blerp: forall (a b: R [i]),
  ((a^* * b^*) = (a * b)^*)%C.
Proof.
  intros a b. destruct a as [ar ai]. destruct b as [br bi]. simpc. rewrite -GRing.opprD. reflexivity.
Qed.

Lemma cprod: forall I (F: I -> R[i]) (r: seq I) P,
  ((\prod_(i <- r | P) F i)^*%C) = \prod_(i <- r | P) (fun x => ((F x)^*)%C) i.
Proof.
  move => I F r P. induction r.
    rewrite !big_nil. apply conjc1.
    rewrite !big_cons. destruct P.
      rewrite -cond_mul_blerp. rewrite IHr. reflexivity.
      apply IHr.
Qed.

(*Lemma conjugate_prod R n mx j:
  (\prod_i (@conjugate R n n mx) i j)%R = conjc (\prod_i mx i j)%R.
Proof.
  unfold conjugate. rewrite cprod. unfold map_mx. apply eq_bigr. intros i _.
  apply mxE.
Qed.

Lemma conjugate_gnarf: forall R n mx (s: perm.perm_of (Phant (ordinal n))),
  \prod_i (@conjugate R n n mx) i (perm.PermDef.fun_of_perm s i) =
  ((\prod_i mx i (perm.PermDef.fun_of_perm s i))^* )%C.
Proof.
  intros R n mx s. simpl. unfold conjugate. rewrite cprod. unfold map_mx.
  apply eq_bigr. intros i _. apply mxE.
Qed.*)

Lemma conjc_opp: forall (a: R[i]), (-(a^*) = (-a)^*)%C.
Proof.
  intros a. destruct a as [ar ai]. simpc. simpl. rewrite GRing.opprK. reflexivity. 
Qed.

Lemma conjcN1: ((-1: R[i])^* )%C = (-1)%C.
Proof.
  rewrite -conjc_opp. rewrite conjc1. reflexivity.
Qed.

Lemma nbn: forall (x y: R [i]), x = y -> -x = -y.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma conjugate_det n (mx: 'M[R [i]]_n):
  (\det (conjugate mx)%C) = ((\det mx)^*%C)%R.
Proof.
  unfold determinant. rewrite csum. apply eq_big_seq. intros x _. rewrite -cond_mul_blerp.
  unfold GRing.exp. destruct (perm.odd_perm x).
    rewrite conjcN1. rewrite !GRing.mulN1r. 
    rewrite cprod. unfold conjugate. unfold map_mx. apply nbn. apply eq_bigr. intros i _. apply mxE.
    rewrite conjc1. rewrite !GRing.mul1r.
    rewrite cprod. unfold conjugate. unfold map_mx. apply eq_bigr. intros i _. apply mxE.
Qed.

Definition abs_sqc (x: R [i]): R := 
  let: (a +i* b)%C := x in a ^+ 2 + b ^+ 2.

Lemma transpose_abs: forall (x: R[i]),
  x * (x^*)%C = ((abs_sqc x)%:C)%C.
Proof.
  destruct x as [a b]. unfold abs_sqc. simpc. rewrite (GRing.mulrC b a). rewrite GRing.addNr. 
  reflexivity.
Qed.

Lemma unitary_det n (mx: 'M[R [i]]_n):
  unitarymx mx -> abs_sqc (\det mx) = 1.
Proof.
  move => unitary_mx.
  assert (((abs_sqc (\det mx))%:C) = 1%:C)%C.
    rewrite -transpose_abs. rewrite -conjugate_det. rewrite GRing.mulrC. rewrite -det_tr.
  rewrite -det_mulmx. rewrite unitary_mx. rewrite det1. auto.
  inversion H. reflexivity.
Qed.

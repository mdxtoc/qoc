From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Parameter R: rcfType.

Definition conjugate m n (mx: 'M[R [i]]_(m, n)) :=
  map_mx conjc mx.

Definition unitarymx (n: nat) (mx: 'M[R [i]]_n) :=
  (conjugate mx)^T *m mx = 1%:M.

Lemma rc_add: forall (a b: R),
  (a%:C + b%:C = (a + b)%:C)%C.
Proof.
  intros a b. unfold real_complex. simpc. reflexivity.
Qed.

Lemma conj_add: forall (a b: R [i]),
  ((a^* + b^*) = (a + b)^*)%C.
Proof.
  intros a b. destruct a as [ar ai]. destruct b as [br bi]. simpc. rewrite -GRing.opprD //. 
Qed.

Lemma conj_mul: forall (a b: R [i]),
  ((a^* * b^*) = (a * b)^*)%C.
Proof.
  intros a b. destruct a as [ar ai]. destruct b as [br bi]. simpc. rewrite -GRing.opprD. reflexivity.
Qed.

Lemma rcsum: forall I (F: I -> R) (r: seq I) P,
  (\sum_(i <- r | P) (F i)%:C)%C = ((\sum_(i <- r | P) F i)%:C)%C.
Proof.
  move => I F r P. induction r.
    rewrite !big_nil //.
    rewrite !big_cons; destruct P;
    [ rewrite IHr; rewrite rc_add //
    | apply IHr
    ].
Qed.
   
Lemma csum: forall I (F: I -> R [i]) (r: seq I) P,
  ((\sum_(i <- r | P) F i)^*%C) = \sum_(i <- r | P) (fun x => ((F x)^*)%C) i.
Proof.
  move => I F r P. induction r.
    rewrite !big_nil. rewrite conjc0 //.
    rewrite !big_cons. destruct P.
      rewrite -conj_add. rewrite IHr. reflexivity.
      apply IHr.
Qed.

Lemma cprod: forall I (F: I -> R[i]) (r: seq I) P,
  ((\prod_(i <- r | P) F i)^*%C) = \prod_(i <- r | P) (fun x => ((F x)^*)%C) i.
Proof.
  move => I F r P. induction r.
    rewrite !big_nil. apply conjc1.
    rewrite !big_cons. destruct P.
      rewrite -conj_mul. rewrite IHr. reflexivity.
      apply IHr.
Qed.

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
  unfold determinant. rewrite csum. apply eq_big_seq. intros x _. rewrite -conj_mul.
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

Lemma conjugate_mulmx: forall m n p (mx1: 'M_(m, n)) (mx2: 'M_(n, p)),
  conjugate (mx1 *m mx2) = conjugate mx1 *m conjugate mx2.
Proof.
  intros m n p mx1 mx2; apply/matrixP; intros x y; rewrite !mxE; rewrite csum; apply eq_bigr;
  intros i _; rewrite !mxE; symmetry; apply conj_mul.
Qed.

Lemma gniarf: forall n (v1 v2: 'cV[R [i]]_n) (mx: 'M[R [i]]_n),
   unitarymx mx -> (conjugate v1)^T *m v2 = (conjugate (mx *m v1))^T *m (mx *m v2).
Proof.
  intros n v1 v2 mx H. rewrite conjugate_mulmx. rewrite trmx_mul. rewrite -mulmxA.
  rewrite[(conjugate mx)^T *m (mx *m v2)]mulmxA. rewrite H. rewrite mul1mx. reflexivity.
Qed.

Lemma bloitbeard:
  forall n (v: 'cV[R [i]]_n),
    ((conjugate v)^T *m v) 0 0 = ((\sum_(i < n) abs_sqc (v i 0))%:C)%C.
Proof.
  intros n v. rewrite !mxE. rewrite -rcsum. apply eq_bigr; intros i _.
  rewrite !mxE. rewrite mulrC. apply transpose_abs.
Qed.

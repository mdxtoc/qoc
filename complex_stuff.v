(* Complex number utility library *)

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
  intros a b; destruct a as [ar ai]; destruct b as [br bi]; simpc; rewrite -GRing.opprD //. 
Qed.

Lemma conj_mul: forall (a b: R [i]),
  ((a^* * b^*) = (a * b)^*)%C.
Proof.
  intros a b; destruct a as [ar ai]; destruct b as [br bi]; simpc; rewrite -GRing.opprD; reflexivity.
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
    rewrite cprod. apply nbn. apply eq_bigr. intros i _. apply mxE.
    rewrite conjc1. rewrite !GRing.mul1r.
    rewrite cprod. unfold conjugate. unfold map_mx. apply eq_bigr. intros i _. apply mxE.
Qed.

Lemma conjugate_mulmx: forall m n p (mx1: 'M_(m, n)) (mx2: 'M_(n, p)),
  conjugate (mx1 *m mx2) = conjugate mx1 *m conjugate mx2.
Proof.
  intros m n p mx1 mx2; apply/matrixP; intros x y; rewrite !mxE; rewrite csum; apply eq_bigr;
  intros i _; rewrite !mxE; symmetry; apply conj_mul.
Qed.

Lemma unitary_preserves_product: forall n (v1 v2: 'cV[R [i]]_n) (mx: 'M[R [i]]_n),
   unitarymx mx -> (conjugate v1)^T *m v2 = (conjugate (mx *m v1))^T *m (mx *m v2).
Proof.
  intros n v1 v2 mx H. rewrite conjugate_mulmx. rewrite trmx_mul. rewrite -mulmxA.
  rewrite[(conjugate mx)^T *m (mx *m v2)]mulmxA. rewrite H. rewrite mul1mx. reflexivity.
Qed.

Lemma conjugate_is_sum:
  forall n (v: 'cV[R [i]]_n),
    ((conjugate v)^T *m v) 0 0 = \sum_(i < n) `|v i 0|^+2.
Proof.
  intros n v. rewrite !mxE. apply eq_bigr; intros i _.
  rewrite !mxE. rewrite mulrC. symmetry; apply sqr_normc.
Qed.

Lemma conj_inv: forall (y: R [i]),
  (y^* ^- 1)%C = ((y ^- 1)^*)%C.
Proof.
  intros y. destruct y as [yr yi]. unfold GRing.inv. simpl. rewrite exprNn. rewrite sqrrN. rewrite expr1n. rewrite mul1r. rewrite mulNr //.
Qed.

Lemma conj_div: forall (x y: R[i]),
  (x^* / y^* = (x / y)^*)%C.
Proof.
  intros x y. destruct x as [a b]; destruct y as [c d]. simpl. 
  unfold GRing.inv at 1. simpc. rewrite sqrrN //.
Qed.

Lemma conj_sqrtc: forall (x: R [i]),
  0 <= x -> sqrtc x = ((sqrtc x)^*)%C.
Proof.
  intros x Hx; rewrite !sqrtc_sqrtr; [ rewrite conjc_real; reflexivity | apply Hx ].
Qed.

Lemma conjc_sqr: forall (x: R[i]),
  (x * x^*)%C = ((Re x) ^+ 2 + (Im x) ^+ 2)%:C%C.
Proof.
  intros [xr xi]. simpc. simpl. rewrite [xi * xr]mulrC. rewrite addNr. reflexivity.
Qed.

Lemma sqrtc_norm: forall (x: R[i]),
  0 <= x -> `|sqrtc x| ^+ 2 = x.
Proof.
  intros x Hx; rewrite sqr_normc; rewrite -conj_sqrtc;
  [ replace (sqrtc x * sqrtc x) with (sqrtc x ^+ 2);
    [ apply sqr_sqrtc
    | auto
    ]
  | apply Hx
  ].
Qed.

Lemma sqrtc_sqr_norm: forall (x: R[i]),
  sqrtc (`|x| ^+ 2) = `|x|.
Proof.
  intros [xr xi]. simpl. rewrite !mulr0. rewrite !oppr0. rewrite !addr0. rewrite !add0r. rewrite !mul0r.
  rewrite !expr0n. rewrite !addr0. rewrite !eq_refl. rewrite !mul1r. rewrite Num.Theory.sqrtr_sqr.
  rewrite Num.Theory.ger0_norm.
  rewrite addrN.
  rewrite -mulr_natr. rewrite mul1r. rewrite mul0r. rewrite Num.Theory.sqrtr0.
  replace ((_ * _) + (_ * _)) with ((Num.sqrt (xr ^+ 2 + xi ^+ 2) ^+ 2) *+ 2); [ | auto ].
  rewrite Num.Theory.sqr_sqrtr. rewrite -mulr_natr. rewrite -mulrA. rewrite divrr. rewrite mulr1.
  reflexivity. apply Num.Theory.unitf_gt0. auto. apply Num.Theory.addr_ge0; apply Num.Theory.sqr_ge0.
  apply Num.Theory.mulr_ge0; apply Num.Theory.sqrtr_ge0.
Qed.

Lemma addr_real_complex: forall (a b: R),
  (a%:C + b%:C)%C = ((a + b)%:C)%C.
Proof.
  intros; unfold GRing.add; simpl; rewrite addr0; apply real_complexE.
Qed.

Lemma oppr_real_complex: forall (a: R),
  (-(a%:C)%C) = ((-a)%:C)%C.
Proof.
  intros; unfold GRing.opp; simpl; rewrite oppr0; apply real_complexE.
Qed.

Lemma subr_real_complex: forall (a b: R),
  (a%:C - b%:C)%C = ((a - b)%:C)%C.
Proof.
  intros; unfold GRing.add; simpl; rewrite oppr0; rewrite addr0; apply real_complexE.
Qed.

Lemma mulr_real_complex: forall (a b: R),
  (a%:C * b%:C)%C = ((a * b)%:C)%C.
Proof.
  intros; unfold GRing.mul; simpl; rewrite !mulr0; rewrite !mul0r; rewrite !oppr0; rewrite !addr0; apply real_complexE.
Qed.
  
Lemma complex_minus_i: 
  forall R: rcfType, (Complex (GRing.zero R) (-1)) = -(Complex 0 1).
Proof.
  intros. unfold GRing.opp. simpl. rewrite oppr0. auto. 
Qed.


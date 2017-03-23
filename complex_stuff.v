From mathcomp Require Import all_ssreflect all_algebra all_field all_character all_fingroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition conjugate (m n: nat) (mx: 'M[algC]_(m, n)) :=
  map_mx conjC mx.

Definition unitarymx (n: nat) (mx: 'M[algC]_n) :=
  (conjugate mx)^T *m mx = 1%:M.

Lemma conj_add: forall (a b: algC),
  ((a^* + b^*) = (a + b)^*)%C.
Proof.
  intros a b. rewrite [a]Crect [b]Crect. rewrite ['Re a + 'i * Im a + _]addrAC. rewrite addrA.
  rewrite -[Re a + Re b + _ + _]addrA. rewrite -['i * Im b + _ * _]mulrDr. rewrite !conjC_rect;
  [ | apply rpred0D | apply rpred0D | .. ]; repeat (apply Creal_Re || apply Creal_Im).
  rewrite addrAC. rewrite addrA. rewrite mulrDr. rewrite -addrA. rewrite -opprB. rewrite opprK. rewrite ['i * Im b + 'i * Im a]addrC //.
Qed.

Lemma conj_mul: forall (a b: algC),
  ((a^* * b^*) = (a * b)^*)%C.
Proof.
  intros a b. rewrite [a]Crect [b]Crect. rewrite mulC_rect.
  rewrite !conjC_rect; [ | apply rpred0D; [ | apply rpredNr ]; apply rpred1M | apply rpred0D; apply rpred1M | ..];
  repeat (apply Creal_Re || apply Creal_Im).
  rewrite mulrDl. rewrite ['Re a * (_ + _)]mulrDr. rewrite [-('i * 'Im a) * (_ - _)]mulrDr. 
  rewrite -mulrN. rewrite [(Re a) * ('i * - 'Im b)]mulrA. rewrite ['Re a * 'i]mulrC. rewrite -['i * 'Re a * - 'Im b]mulrA.
  rewrite -mulrN. rewrite ['i * - 'Im a * ('i * - 'Im b)]mulrAC. rewrite ['i * ('i* - 'Im b)]mulrA.
  replace ('i * 'i) with (('i:algC) ^+ 2). rewrite sqrCi. rewrite mulNr. rewrite mul1r. rewrite opprK. rewrite -mulrA.
  rewrite -['Re a * 'Re b + 'i * _ + _]addrA. rewrite ['i * _ + (_ + _)]addrA. rewrite [(_ + _) + ('Im b * _)]addrC.
  rewrite addrA. rewrite -mulrDr. rewrite mulrN. rewrite ['Im b * _ ]mulrC. 
  rewrite mulrN. rewrite mulNr. rewrite ['Im a * _]mulrC. rewrite -opprD. rewrite mulrN //.
  auto.
Qed.

Lemma csum: forall I (r: seq I) P (F: _ -> algC),
  conjC (\sum_(i <- r | P) F i) = \sum_(i <- r | P) (fun x => conjC (F x)) i.
Proof.
  intros I r P F; induction r;
  [ rewrite !big_nil; apply conjC0
  | rewrite !big_cons; destruct P; try rewrite -conj_add; rewrite IHr //
  ].
Qed.

Lemma cprod: forall I (r: seq I) P (F: _ -> algC),
  conjC (\prod_(i <- r | P) F i) = \prod_(i <- r | P) (fun x => conjC (F x)) i.
Proof.
  intros I r P F; induction r;
  [ rewrite !big_nil; apply conjC1
  | rewrite !big_cons; destruct P; try rewrite -conj_mul; rewrite IHr //
  ].
Qed.

Lemma blerp: forall (R: ringType) (a b: R), -(a + b) = -a - b.
Proof.
  intros. rewrite -opprB. rewrite opprK. rewrite addrC //.
Qed.

Lemma conjc_opp: forall (a: algC), (-(a^*) = (-a)^*)%C.
Proof.
  intros a. rewrite [a]Crect. rewrite blerp. rewrite -conjC_rect; [ | apply rpredNr; apply Creal_Re | apply Creal_Im].
  rewrite conjCK. rewrite conjC_rect; [ | apply Creal_Re | apply Creal_Im ]. rewrite opprB. rewrite addrC //.
Qed.

Lemma conjcN1: ((-1: algC)^* )%C = (-1)%C.
Proof.
  rewrite -conjc_opp. rewrite conjC1 //. 
Qed.

Lemma nbn: forall (x y: algC), x = y -> -x = -y.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma conjugate_det n (mx: 'M[algC]_n):
  (\det (conjugate mx)%C) = ((\det mx)^*%C)%R.
Proof.
  unfold determinant. rewrite csum. apply eq_big_seq. intros x _. rewrite -conj_mul.
  unfold GRing.exp. destruct (perm.odd_perm x).
    rewrite conjcN1. rewrite !GRing.mulN1r. 
    rewrite cprod. unfold conjugate. unfold map_mx. apply nbn. apply eq_bigr. intros i _. apply mxE.
    rewrite conjC1. rewrite !GRing.mul1r.
    rewrite cprod. unfold conjugate. unfold map_mx. apply eq_bigr. intros i _. apply mxE.
Qed.

Definition abs_sqc (x: algC) := 
   ('Re x) ^+ 2 + ('Im x) ^+ 2.

Lemma abs_sqc_eq: forall x,
  abs_sqc x = ((`|x| ^+ 2))%C.
Proof.
  intros x. unfold abs_sqc. rewrite [x]Crect. rewrite Re_rect; [ | apply Creal_Re | apply Creal_Im ].
  rewrite Im_rect; [ | apply Creal_Re | apply Creal_Im ]. rewrite normCK. rewrite conjC_rect; [ | apply Creal_Re | apply Creal_Im ].
  rewrite mulrDr. rewrite !mulrDl. 
  rewrite -addrA. rewrite ['i * 'Im x * 'Re x + (_ + _)]addrA. rewrite [('i * 'Im x * 'Re x + _) + _]addrC. rewrite addrA.
  rewrite !mulrN. rewrite ['Re x * ('i * _)]mulrC. rewrite addrN. rewrite addr0.
  rewrite -['i * _ * _]mulrA. rewrite ['Im x * (_ * _)]mulrA. rewrite [('Im x * _)]mulrC. rewrite -[('i * 'Im x) * 'Im x]mulrA.
  rewrite ['i * ('i * _)]mulrA. replace ('i * 'i) with (('i:algC) ^+ 2). rewrite sqrCi. rewrite mulNr. rewrite mul1r. rewrite opprK //.
  auto.
Qed.

Lemma unitary_det n (mx: 'M[algC]_n):
  unitarymx mx -> abs_sqc (\det mx) = 1.
Proof.
  move => unitary_mx. rewrite abs_sqc_eq. rewrite normCK. rewrite -conjugate_det. rewrite mulrC. rewrite -det_tr.
  rewrite -det_mulmx. rewrite unitary_mx. rewrite det1 //.
Qed.



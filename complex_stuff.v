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

Lemma conjugate_det (n: nat) (mx: 'M[algC]_n):
  (\det (conjugate mx) = ((\det mx)^*%C))%R.
Proof.
  unfold determinant. rewrite csum. apply eq_big_seq. unfold mem. unfold prop_in1. intros.
  rewrite -conj_mul. unfold conjugate. unfold map_mx. rewrite cprod. replace ((-1:algC) ^+ x)^* with ((-1:algC) ^+ x). 
  
Lemma unitary_det R n mx:
  (@unitarymx R n mx) -> (\det mx)%R = 1%R.
Proof.
  move => unitary_mx. rewrite -(det1 _ n). rewrite -unitary_mx //. rewrite det_mulmx. rewrite det_tr.







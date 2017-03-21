From mathcomp Require Import all_ssreflect all_real_closed all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import complex_stuff.

Local Open Scope ring_scope.
Definition abs_sqc (R: rcfType) (x: R [i]): R := 
  let: (a +i* b)%C := x in a ^+ 2 + b ^+ 2.

Record qubit_mixin_of (R: rcfType) (n: nat) := QubitMixin {
  vector: 'cV[R [i]]_(2 ^ n);
  vector_is_unit: is_true (\sum_(i < 2^n) (abs_sqc (vector i (Ordinal (ltnSn 0)))) == 1)
}.

Definition conjugate (R: rcfType) (m n: nat) (mx: 'M[R [i]]_(m, n)) :=
  map_mx conjc mx.

Definition conjugate_transpose (R: rcfType) (m n: nat) (mx: 'M[R [i]]_(m, n)) :=
  (trmx (conjugate mx)).

Definition unitarymx (R: rcfType) (n: nat) (mx: 'M[R [i]]_n) :=
  (conjugate_transpose mx) *m mx = 1%:M.

Lemma cond_add_blerp: forall (R: rcfType) (a b: R [i]),
  ((a^* + b^*) = (a + b)^*)%C.
Proof.
  intros R a b. destruct a as [ar ai]. destruct b as [br bi]. simpc. rewrite -GRing.opprD. reflexivity.
Qed.

Lemma cond_mul_blerp: forall (R: rcfType) (a b: R [i]),
  ((a^* * b^*) = (a * b)^*)%C.
Proof.
  intros R a b. destruct a as [ar ai]. destruct b as [br bi]. simpc. rewrite -GRing.opprD. reflexivity.
Qed.

Lemma cprod: forall (R: rcfType) (n: nat) (F: 'I_n -> R[i]),
  conjc (\prod_i F i) = \prod_i (fun x => conjc (F x)) i.
Proof.
  intros R n F. induction n.
    rewrite !big_ord0. apply/conjc1.
    rewrite big_ord_recl. rewrite -cond_mul_blerp. rewrite IHn. rewrite big_ord_recl. reflexivity.
Qed.

Lemma conjugate_prod R n mx j:
  (\prod_i (@conjugate R n n mx) i j)%R = conjc (\prod_i mx i j)%R.
Proof.
  unfold conjugate. rewrite cprod. unfold map_mx. apply eq_bigr. intros i _. apply mxE.
Qed.

Lemma conjugate_det R n mx:
  (\det (@conjugate R n n mx) = ((\det mx)^*%C))%R.
Proof.
  unfold determinant. rewrite (eq_big_seq .
Lemma unitary_det R n mx:
  (@unitarymx R n mx) -> (\det mx)%R = 1%R.
Proof.
  move => unitary_mx. rewrite -(det1 _ n). rewrite -unitary_mx //. rewrite det_mulmx. rewrite det_tr.


Lemma unitary1 R n mx:
  (@unitarymx R n mx) -> (mulmx mx (conjugate_transpose mx)) = (1%:M)%R.
Proof.
  move=> unitary_mx. rewrite -unitary_mx. 
Record gate_mixin_of (R: rcfType) (n: nat): Type := GateMixin {
  gate: 'M[R [i]]_(2 ^ n);
  gate_is_unitary: is_true (unitarymx gate)
}.

Lemma blerp: forall R n q g, is_true
   ((\sum_(i < 2 ^ n)
        abs_sqc
          (((@gate R n g) *m vector q) i (Ordinal (n:=1) (m:=0) (ltnSn 0))))%R ==
    1%R).
Proof.
  intros R n q g; destruct q as [q Hq]; destruct g as [g Hg]; simpl.

Definition apply (R: rcfType) (n: nat) (q: qubit_mixin_of R n) (g: gate_mixin_of R n): qubit_mixin_of R n :=
  QubitMixin R n
    ((gate R n g) *m (vector R n q))%R
    _.





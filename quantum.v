From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import complex_stuff.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Record qubit_mixin_of (n: nat) := QubitMixin {
  vector: 'cV[algC]_(2 ^ n);
  vector_is_unit: \sum_(i < 2^n) (`|vector i (Ordinal (ltnSn 0))|^+2) = 1
}.

Record gate_mixin_of (n: nat): Type := GateMixin {
  gate: 'M[algC]_(2 ^ n);
  gate_is_unitary: unitarymx gate
}.

Lemma blerp: forall n q g, 
   (\sum_(i < 2 ^ n)
        `|((gate g) *m vector q) i (Ordinal (n:=1) (m:=0) (ltnSn 0))| ^+2) =
    1%R.
Proof.
  intros n q g; destruct q as [q Hq]; destruct g as [g Hg]; simpl.
  rewrite -bloitbeard. rewrite -gniarf; [ | apply Hg ].
  unfold trmx. unfold conjugate. rewrite mxE. rewrite -Hq. apply eq_big;
  [ auto | intros i _].
    unfold map_mx. rewrite !mxE. rewrite ord1. rewrite normCK. apply mulrC.
Qed.

Definition apply (n: nat) (q: qubit_mixin_of n) (g: gate_mixin_of n): qubit_mixin_of n :=
  QubitMixin 
    (blerp q g).





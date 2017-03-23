From mathcomp Require Import all_ssreflect all_real_closed all_algebra all_field.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import complex_stuff.

Local Open Scope ring_scope.

Record qubit_mixin_of (n: nat) := QubitMixin {
  vector: 'cV[algC]_(2 ^ n);
  vector_is_unit: is_true (\sum_(i < 2^n) (`|vector i (Ordinal (ltnSn 0))|^+2) == 1)
}.

Record gate_mixin_of (n: nat): Type := GateMixin {
  gate: 'M[algC]_(2 ^ n);
  gate_is_unitary: unitarymx gate
}.

Lemma blerp: forall n q g, is_true
   ((\sum_(i < 2 ^ n)
        `|((gate g) *m vector q) i (Ordinal (n:=1) (m:=0) (ltnSn 0))| ^+2) ==
    1%R).
Proof.
  intros n q g; destruct q as [q Hq]; destruct g as [g Hg]; simpl.
  

Definition apply (R: rcfType) (n: nat) (q: qubit_mixin_of R n) (g: gate_mixin_of R n): qubit_mixin_of R n :=
  QubitMixin R n
    ((gate R n g) *m (vector R n q))%R
    _.





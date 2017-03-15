From mathcomp Require Import all_ssreflect all_real_closed all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Require Import complex_random_stuff.

Record qubit_mixin_of (R: rcfType) (n: nat) := QubitMixin {
  vector: 'cV[R [i]]_(2 ^ n);
  vector_is_unit: is_true (\sum_(i < 2^n) (abs_sqc (vector i (Ordinal (ltnSn 0)))) == 1)
}.

Record gate_mixin_of (R: rcfType) (n: nat): Type := GateMixin {
  gate: 'M[R [i]]_(2 ^ n);
  gate_is_unitary: unitarymx gate
}.

Axiom blerp: forall R n q g, is_true
   ((\sum_(i < 2 ^ n)
        abs_sqc
          (((@gate R n g) *m vector q) i (Ordinal (n:=1) (m:=0) (ltnSn 0))))%R ==
    1%R).
(*Proof.
  intros R n q g; destruct q as [q Hq]; destruct g as [g Hg]; simpl.*)

Definition apply (R: rcfType) (n: nat) (q: qubit_mixin_of R n) (g: gate_mixin_of R n): qubit_mixin_of R n :=
  QubitMixin 
    (blerp q g).





Require Import ssreflect.
Require Import complex.
Require Import ssrnum.
Require Import matrix.
Require Import fintype.
Require Import ssrnat.
(*Require Import bigop.*)
Require Import ssralg.
(*Require Import mxalgebra.*)
Require Import eqtype.

Open Scope complex_scope.

Definition abs_sqc (R: rcfType) (x: R [i]) := 
  let: a +i* b := x in (a ^+ 2 + b ^+ 2)%R.

Record qubit_mixin_of (R: rcfType) (n: nat): Type := QubitMixin {
  vector: 'cV[R [i]]_(2 ^ n);
  vector_is_unit: is_true ((\sum_(i < 2^n) (abs_sqc _ (vector i (Ordinal (ltnSn 0)))))%R == 1%R)
}.

Record gate_mixin_of (R: rcfType) (n: nat): Type := GateMixin {
  gate: 'M[R [i]]_(2 ^ n);
  (* XXX needs to be added: gate_is_unitary *)
}.
  







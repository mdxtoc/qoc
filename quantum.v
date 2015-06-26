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

Variable R: rcfType.

Definition qubit (n: nat): Type :=
  {m: 'M[R [i]]_(2^n, 1) | is_true ((\sum_(i < 2^n) (m i (Ordinal (ltnSn 0))))%R == 1%R) }.








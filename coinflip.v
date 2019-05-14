Set Implicit Arguments.

From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Local Open Scope ring_scope.
Import Num.Theory GRing.Theory.

Require Import other_stuff.
Require Import IMonad quantum_monad.
Require Import quantum.


Lemma zero_qubitP: 
  \sum_(i < 2^1) `|('M{[:: [:: 1]; [:: 0]]}: 'cV[complex_stuff.R[i]]_(2^1)) i 0| ^+ 2 == 1.
Proof.
  intros; rewrite big_ord_recl; rewrite big_ord1;
  rewrite !mxE; rewrite !normc_def; rewrite !expr0n !expr1n;
  rewrite !addr0; rewrite !sqrtr0 !sqrtr1; rewrite !expr0n !expr1n;
  rewrite !addr0 //.
Qed.
Canonical zero_qubit := QubitVector zero_qubitP.

Lemma one_qubitP:
  \sum_(i < 2^1) `|('M{[:: [::0]; [:: 1]]}: 'cV[complex_stuff.R[i]]_(2^1)) i 0| ^+ 2 == 1.
Proof.
  intros. rewrite big_ord_recl. rewrite big_ord1.
  rewrite !mxE; rewrite !normc_def; rewrite !expr0n !expr1n;
  rewrite !addr0; rewrite !sqrtr0 !sqrtr1; rewrite !expr0n !expr1n; rewrite !add0r //.
Qed.
Canonical one_qubit := QubitVector one_qubitP.

Program Definition coinflip :=
  qio_bind
  (MkQbit (A:=bool) (i:=0) (o:=1) zero_qubit (QReturn true))
  (fun q => ApplyU hadamard_gate (QReturn true)).

Time Let x := Eval native_compute in (evalQIO coinflip (cons (1%:R, quantum.zero_qubit) nil)).
Print x.

Let y := Eval compute in length x.
Print y.
From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Require Import complex_stuff.

Record qubit_mixin_of (n: nat) := QubitMixin {
  vector: 'cV[complex_stuff.R [i]]_(2 ^ n);
  vector_is_unit: ((\sum_(i < 2^n) (abs_sqc (vector i 0)))%:C = 1)%C
}.

Record gate_mixin_of (n: nat): Type := GateMixin {
  gate: 'M[complex_stuff.R [i]]_(2 ^ n);
  gate_is_unitary: unitarymx gate
}.

Lemma blerp: forall n q g,
  ((\sum_(i < 2 ^ n) (abs_sqc (((gate g) *m vector q) i 0)))%:C = 1)%C.
Proof.
  intros n q g; destruct q as [q Hq]; destruct g as [g Hg]; simpl.
  rewrite -bloitbeard. rewrite -gniarf;
  [ rewrite !mxE; rewrite -Hq; rewrite -rcsum; apply eq_bigr; intros i _;
    rewrite mulrC; rewrite !mxE; apply transpose_abs
  | apply Hg
  ]. 
Qed.

Definition apply (n: nat) (q: qubit_mixin_of n) (g: gate_mixin_of n): qubit_mixin_of n :=
  QubitMixin 
    (blerp q g).

Definition seq2matrix (T: ringType) m n (l: seq (seq T)) :=
  \matrix_(i<m,j<n) nth 1 (nth [::] l i) j.

Local Notation "''M{' l } " := (seq2matrix _ _ l).

Definition I_matrix: 'M[R [i]]_2 :=
  'M{[:: [:: 1; 0];
         [:: 0; 1]]}.

(* this can probably be done by a tactic, or computationally *)
Lemma I_unitary: unitarymx I_matrix.
Proof.
  unfold unitarymx. unfold I_matrix. unfold conjugate. unfold mulmx. unfold map_mx. apply/matrixP. intros x y.
  rewrite !mxE. rewrite !big_ord_recl. rewrite big_ord0. rewrite !mxE. 
  destruct x as [m H]; destruct m as [ | m]; destruct y as [m' H']; destruct m' as [ | m']; 
  [ 
  | destruct m' as [ | m'];
    [ 
    | absurd (m'.+2 < 2)%N; auto; apply H'
    ]
  | destruct m as [ | m ];
    [
    | absurd (m.+2 < 2)%N; auto; apply H
    ]
  | destruct m as [ | m ];
    [ destruct m' as [ | m' ];
      [ 
      | absurd (m'.+2 < 2)%N; auto; apply H'
      ]
    | absurd (m.+2 < 2)%N; auto; apply H
    ]
  ]; simpl;
  repeat try ( rewrite conjC1 || rewrite conjC0 || rewrite mul1r || rewrite mulr0 || rewrite addr0 || rewrite mul0r || rewrite add0r);
  reflexivity.
Qed.

Definition I_gate := (@GateMixin 1 I_matrix I_is_unitary).

Definition X_matrix: 'M[R [i]]_2 :=
  'M{[:: [:: 0; 1];
         [:: 1; 0]]}.

Definition Y_matrix: 'M[R [i]]_2 :=
  ('M{[:: [:: 0; -'i];
          [:: 'i; 0]]})%C.

Definition Z_matrix: 'M[R [i]]_2 :=
  'M{[:: [:: 1; 0];
         [:: 0; -1]]}.

Definition hadamard_matrix: 'M[R [i]]_2 :=
  ('M{[:: [:: (1/Num.sqrt (2%:R))%:C; (1/Num.sqrt (2%:R))%:C];
          [:: (1/Num.sqrt (2%:R))%:C; -(1/Num.sqrt (2%:R))%:C]]})%C.

Definition measure n (bit: 'I_n) (qubit: qubit_mixin_of n): 
  (qubit_mixin_of n * qubit_mixin_of n).


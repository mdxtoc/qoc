From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Require Import complex_stuff.

Record qubit_mixin_of (n: nat) := QubitMixin {
  vector: 'cV[complex_stuff.R [i]]_(2 ^ n);
  vector_is_unit: \sum_(i < 2^n) `|vector i 0|^+2 = 1
}.

Record gate_mixin_of (n: nat): Type := GateMixin {
  gate: 'M[complex_stuff.R [i]]_(2 ^ n);
  gate_is_unitary: unitarymx gate
}.

Lemma blerp: forall n q g,
  \sum_(i < 2 ^ n) `|(gate g *m vector q) i 0|^+2 = 1.
Proof.
  intros n q g; destruct q as [q Hq]; destruct g as [g Hg]; simpl.
  rewrite -bloitbeard. rewrite -gniarf;
  [ rewrite !mxE; rewrite -Hq; apply eq_bigr; intros i _;
    rewrite mulrC; rewrite !mxE; symmetry; apply sqr_normc
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
  apply/matrixP. intros x y; rewrite !mxE. rewrite !big_ord_recl. rewrite big_ord0; rewrite !mxE.
  destruct x as [m H]; destruct m as [ | m]; destruct y as [m' H']; destruct m' as [ | m'];
  [ 
  | destruct m' as [ | m'];
    [ rewrite mulr0; rewrite add0r; rewrite addr0
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
  ]; simpl; try repeat (rewrite mulr0 || rewrite mul0r || rewrite addr0 || rewrite add0r || rewrite mul1r || rewrite mulr1);
  rewrite oppr0 //.
Qed.

Definition I_gate := (@GateMixin 1 I_matrix I_unitary).

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

Definition select n (i: 'I_(2^n)) (bit: 'I_n) :=
  (i %% (2^(bit + 1)) >= 2^bit)%N.

Definition measure_1 n (bit: 'I_n) (qubit: qubit_mixin_of n) :=
  \col_(i < 2^n)
      if select i bit
      then ((vector qubit) i 0) / \sum_(i < 2^n | select i bit) ((vector qubit) i 0)^+2
      else 0.

Lemma mulc_real: forall (x y: R),
  ((x%:C * y %:C) = (x * y)%:C)%C.
Proof.
  intros. rewrite !real_complexE. simpc. auto.
Qed.

Lemma leq_Re: forall (x: R[i]), 0 <= x -> 0 <= Re x.
Proof.
  intros [xr xi]; unfold Num.Def.ler. simpl. destruct (xi == 0) eqn:H; rewrite H; simpl; auto.
Qed.

Lemma bloit: forall (x: R[i]), x != 0 -> `|x| != 0.
Proof.
  intros x H. apply contra with (x == 0). intros. apply/eqP. apply Num.Theory.normr0_eq0. apply/eqP. apply H0. apply H.
Qed.

(*Lemma znoits: forall (x: R[i]), x != 0 -> ComplexField.normc x != 0.
Proof.
  intros x H. apply contra with (x == 0). intros; apply/eqP; apply ComplexField.eq0_normc; apply/eqP; apply H0; apply H.
Qed.*)

Lemma measure_two: forall (a b: R[i]), a != 0 -> b != 0 ->
  `|a / sqrtc (`|a|^+2 + `|b|^+2)| ^+ 2 + `|b / sqrtc (`|a|^+2 + `|b|^+2)| ^+ 2 = 1.
Proof.
  intros a b Ha Hb. rewrite !sqr_normc. rewrite -!conj_div. rewrite !mulf_div. rewrite -!sqr_normc. rewrite -mulrDl.
  rewrite [`|sqrtc _| ^+ 2]sqr_normc. rewrite sqrtc_sqrtr; [ | apply Num.Theory.addr_ge0; rewrite sqr_normc; apply mulcJ_ge0 ]. rewrite conjc_real.
  rewrite mulc_real. rewrite !real_complexE. 
  replace (Num.sqrt (Re (`|a| ^+ 2 + `|b| ^+ 2)) * _) with
   (Num.sqrt (Re (`|a| ^+ 2 + `|b| ^+ 2)) ^+ 2); [ | auto ]. rewrite Num.Theory.sqr_sqrtr; [ |
     apply leq_Re; apply Num.Theory.addr_ge0; rewrite sqr_normc; apply mulcJ_ge0 ]. rewrite -real_complexE. rewrite RRe_real;
     [ rewrite mulrV //
     | apply/complex_realP; exists (Num.sqrt (Re a ^+ 2 + Im a ^+ 2) ^+ 2 + Num.sqrt (Re b ^+ 2 + Im b ^+ 2) ^+ 2);
       rewrite !normc_def; simpc; auto
     ].
     apply/unitrP; exists ((`|a|^+2 + `|b|^+2)^-1); split; [ | rewrite GRing.mulrC ]; apply ComplexField.mulVc;
     apply Num.Theory.lt0r_neq0; apply Num.Theory.addr_gt0; apply Num.Theory.exprn_gt0; rewrite Num.Theory.ltr_def; apply/andP;
     split; try apply bloit; try apply Ha || apply Hb; rewrite normc_def; rewrite real_complexE;
     unfold Num.Def.ler; simpl; apply/andP; split; try apply Num.Theory.sqrtr_ge0; auto.
Qed.

Lemma measure_aux: forall (r: seq R[i]), 
  (\sum_(i <- r) `|i|^+2) \is a GRing.unit ->
  \sum_(i <- r) `|i / sqrtc (\sum_(i <- r) `|i|^+2)|^+2 = 1.
Proof.
  intros r. destruct r; 
  [ rewrite !big_nil; intros H; absurd (((0:R)%:C)%C \is a GRing.unit);
    [ rewrite unitr0 //
    | apply H
    ] 
  | rewrite !big_cons
  ]. 
(*  intros H.
  rewrite sqrtc_sqr_norm. rewrite Num.Theory.normrM. rewrite Num.Theory.normrV. rewrite Num.Theory.normr_id.
  rewrite divrr. rewrite expr1n. reflexivity.
  rewrite -(@unitrX_pos _ _ 2); [ apply H | auto ].
  rewrite -(@unitrX_pos _ _ 2); [ apply H | auto ].
  intros H. *)

Lemma measure_unitary: forall n b q, \sum_(i < 2^n) `|(measure_1 b q) i 0|^+2 = 1.
Proof.
  move=> n b q. 

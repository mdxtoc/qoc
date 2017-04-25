From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Num.Theory GRing.Theory.

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
  rewrite -gniarf. rewrite -unitary_preserves_product;
  [ rewrite !mxE; rewrite -Hq; apply eq_bigr; intros i _;
    rewrite mulrC; rewrite !mxE; symmetry; apply sqr_normc
  | apply Hg
  ]. 
Qed.

Definition apply (n: nat) (q: qubit_mixin_of n) (g: gate_mixin_of n): qubit_mixin_of n :=
  QubitMixin 
    (blerp q g).

(* this is more general, can go to a utils file *)
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
      then `|(vector qubit) i 0 / sqrtc (\sum_(i < 2^n | select i bit) `|(vector qubit) i 0|^+2)|^+2
      else 0.

Lemma measure_aux: forall I (r: seq I) P (F: I -> R[i]), 
  (\sum_(i <- r | P i) `|F i|^+2) \is a GRing.unit ->
  \sum_(i <- r | P i) (`|F i / sqrtc (\sum_(i <- r | P i) `|F i|^+2)|^+2) = 1.
Proof.
  intros I r P F; destruct r;
  [ rewrite !big_nil; intros H; absurd (((0:R)%:C)%C \is a GRing.unit);
    [ rewrite unitr0 //
    | apply H
    ] 
  | rewrite !big_cons; destruct (P i); intros H;
    [ rewrite normf_div; rewrite expr_div_n; replace (\sum_(j <- r | P j) `|F j / sqrtc _| ^+ 2) with
      (\sum_(j <- r | P j) `|F j| ^+ 2 / `|sqrtc (`|F i| ^+ 2 + \sum_(j0 <- r | P j0) `|F j0| ^+ 2)| ^+ 2);
      [ rewrite -mulr_suml; rewrite -mulrDl; rewrite sqrtc_norm;
        [ rewrite divrr; [ reflexivity | apply H ]
        | apply addr_ge0; [ apply exprn_ge0; apply normr_ge0 | apply sumr_ge0; intros x _; apply exprn_ge0; apply normr_ge0 ]
        ]
      | apply eq_bigr; intros x _; rewrite Num.Theory.normf_div; rewrite expr_div_n //
      ]
    | replace (\sum_(j <- r | P j) `|F j / sqrtc _| ^+ 2) with
      (\sum_(j <- r | P j) `|F j|^+2 / `|sqrtc (\sum_(j0 <- r | P j0) `|F j0|^+2)|^+2);
      [ rewrite -mulr_suml; rewrite sqrtc_norm;
        [ rewrite divrr; [ reflexivity | apply H ]
        | apply sumr_ge0; intros x _; apply exprn_ge0; apply normr_ge0
        ]
      | apply eq_bigr; intros x _; rewrite normf_div; rewrite expr_div_n //
      ]
    ]
  ].
Qed.

(* this is more general, can go to a utils file *)
Lemma sumr_cond_if: forall (T: ringType) I (r: seq I) P (F: I -> T),
  \sum_(i <- r | P i) F i = \sum_(i <- r) (fun x => if P x then F x else (0:T)) i.
Proof.
  intros T I r P F; induction r;
  [ rewrite !big_nil //
  | rewrite !big_cons; destruct (P a);
    [ rewrite IHr //
    | rewrite add0r; apply IHr
    ]
  ].
Qed.

Lemma sum_mul_dist: forall (T: ringType) m n (F: 'I_m -> T) (G: 'I_n -> T), 
  (\sum_(i < m) F i) * (\sum_(j < n) G j) =
  \sum_(i < m) F i * \sum_(j < n) G j.
Proof.
  intros. induction m;
  [ rewrite !big_ord0; apply mul0r
  | rewrite !big_ord_recl; rewrite mulrDl; rewrite IHm //
  ].
Qed.

Lemma measure_unitary: forall n b q,
  \sum_(i < 2^n | select i b) `|(vector q) i 0| ^+ 2 \is a GRing.unit -> 
  \sum_(i < 2^n) (measure_1 b q) i 0 = 1.
Proof.
  move=> n b q H. unfold measure_1.
  replace (\sum_(i < 2 ^ n) (\col_i0 _) i 0) with
    (\sum_(i < 2^n) (if select i b then `|vector q i 0 / sqrtc (\sum_(i1 < 2 ^ n | select i1 b) `|(vector q) i1 0| ^+2)| ^+ 2 else 0)).
  2: apply eq_bigr; intros i _; rewrite mxE //.
  rewrite -!sumr_cond_if. apply measure_aux. apply H.
Qed.

Lemma glerq: forall n m, ((2^n * 2^m = 2^(n+m))%N * ((1*1) = S 0)%N)%type.
Proof.
  intros n m. split.
    symmetry; apply expnD. 
    auto.
Qed.

Lemma znoits: forall n m q1 q2,
  \sum_(i < 2^(n+m)) `|(castmx (glerq n m) (vector q1 *t vector q2)) i 0| ^+ 2 = 1.
Proof.
  intros m n q1 q2; destruct q1 as [q1 Hq1]; destruct q2 as [q2 Hq2]; simpl. 
  transitivity (\sum_(i < 2^m*2^n) `|q1 (mxtens_unindex i).1 (mxtens_unindex (m:=1) (n:=1) 0).1| ^+ 2 * `|q2 (mxtens_unindex i).2 (mxtens_unindex (m:=1) (n:=1) 0).2| ^+ 2).
  replace (index_enum (ordinal_finType (2^(m+n)))) with (index_enum (ordinal_finType (2^m * 2^n))).
  rewrite mxE. rewrite normrM. rewrite exprMn //.
  rewrite -(mulr_sum (fun x => `|q1 x (mxtens_unindex (m:=1) (n:=1) 0).1| ^+ 2) (fun x => `|q2 x (mxtens_unindex (m:=1) (n:=1) 0).2| ^+ 2)).
  rewrite sum_mul_dist. simpl.
  (* This can probably be done in a much easier way, but you know... *)
  replace (\sum_(j<2^n) `|q2 j _|^+2) with (1:R[i]).
  rewrite (eq_bigr _ (fun P x => mulr1 _)).
  replace (\sum_(i<2^m) `|q1 i _|^+2) with (1:R[i]). reflexivity.
    rewrite -Hq1. apply eq_bigr. intros i _. replace (q1 i 0) with (q1 i (Ordinal (mxtens_index_proof1 (m:=1) (n:=1) 0))).
      reflexivity. transitivity (q1 i (Ordinal (ltn0Sn 0))). replace (Ordinal (ltn0Sn 0)) with (Ordinal (mxtens_index_proof1 (m:=1) (n:=1) 0)).
      reflexivity. apply/val_eqP. simpl. auto.
      reflexivity.
    rewrite -Hq2. apply eq_bigr. intros i _. replace (q2 i 0) with (q2 i (Ordinal (mxtens_index_proof2 (m:=1) (n:=1) 0))).
      reflexivity. transitivity (q2 i (Ordinal (ltn0Sn 0))). replace (Ordinal (ltn0Sn 0)) with (Ordinal (mxtens_index_proof2 (m:=1) (n:=1) 0)).
      reflexivity. apply/val_eqP. simpl. auto.
      reflexivity.
Qed.*)

Definition combine (n m: nat) (q1: qubit_mixin_of n) (q2: qubit_mixin_of m): (qubit_mixin_of (n+m)) :=
  QubitMixin (znoits q1 q2).
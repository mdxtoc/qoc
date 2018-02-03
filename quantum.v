(* Main quantum library *)

From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Num.Theory GRing.Theory.

Require Import other_stuff complex_stuff.

Record qubit_mixin_of (n: nat) := QubitMixin {
  vector: 'cV[complex_stuff.R [i]]_(2 ^ n);
  vector_is_unit: \sum_(i < 2^n) `|vector i 0|^+2 = 1
}.

Record gate_mixin_of (n: nat): Type := GateMixin {
  gate: 'M[complex_stuff.R [i]]_(2 ^ n);
  gate_is_unitary: unitarymx gate
}.

Program Definition apply (n: nat) (q: qubit_mixin_of n) (g: gate_mixin_of n): qubit_mixin_of n :=
  (@QubitMixin _ (gate g *m vector q) _).
Obligation 1.
  intros n q g; destruct q as [q Hq]; destruct g as [g Hg]; simpl.
  rewrite -conjugate_is_sum. rewrite -unitary_preserves_product;
  [ rewrite !mxE; rewrite -Hq; apply eq_bigr; intros i _;
    rewrite mulrC; rewrite !mxE; symmetry; apply sqr_normc
  | apply Hg
  ]. 
Qed.

Definition I_matrix: 'M[R [i]]_2 :=
  'M{[:: [:: 1; 0];
         [:: 0; 1]]}.

Program Definition I_gate := (@GateMixin 1 I_matrix _).
Obligation 1.
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

Definition X_matrix: 'M[R [i]]_2 :=
  'M{[:: [:: 0; 1];
         [:: 1; 0]]}.

Program Definition X_gate := (@GateMixin 1 X_matrix _).
Obligation 1.
  apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl; rewrite big_ord0; rewrite !mxE;
  destruct x as [[ | [ | x]] Hx]; destruct y as [[ | [ | y]] Hy]; simpl;
  try (absurd (x.+2 < 2)%N; auto); try (absurd (y.+2 < 2)%N; auto);
  try repeat (rewrite mul0r || rewrite mulr0 || rewrite mulr1 || rewrite addr0 || rewrite add0r || rewrite oppr0 || rewrite mulNr || rewrite mulrN);
  auto.
Qed.

Definition Y_matrix: 'M[R [i]]_2 :=
  ('M{[:: [:: 0; -'i];
          [:: 'i; 0]]})%C.

Program Definition Y_gate := (@GateMixin 1 Y_matrix _).
Obligation 1.
  apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl; rewrite big_ord0; rewrite !mxE;
  destruct x as [[ | [ | x]] Hx]; destruct y as [[ | [ | y]] Hy]; simpl;
  try (absurd (x.+2 < 2)%N; auto); try (absurd (y.+2 < 2)%N; auto);
  try repeat (rewrite mul0r || rewrite mulr0 || rewrite mulr1 || rewrite addr0 || rewrite add0r || rewrite oppr0 || rewrite mulNr || rewrite mulrN || rewrite opprK || rewrite -expr2 || rewrite sqr_i || rewrite complex_minus_i);
  auto.
Qed.

Definition Z_matrix: 'M[R [i]]_2 :=
  'M{[:: [:: 1; 0];
         [:: 0; -1]]}.

Program Definition Z_gate := (@GateMixin 1 Z_matrix _ ).
Obligation 1.
  apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl; rewrite big_ord0; rewrite !mxE;
  destruct x as [[ | [ | x]] Hx]; destruct y as [[ | [ | y]] Hy]; simpl;
  try (absurd (x.+2 < 2)%N; auto); try (absurd (y.+2 < 2)%N; auto);
  try repeat (rewrite mul0r || rewrite mulr0 || rewrite mulr1 || rewrite addr0 || rewrite add0r || rewrite oppr0 || rewrite mulNr || rewrite mulrN);
  auto;
  rewrite -oppr0; unfold GRing.opp; simpl; rewrite !opprK //.
Qed.

Definition hadamard_matrix: 'M[R [i]]_2 :=
  ('M{[:: [:: (1/Num.sqrt (2%:R))%:C; (1/Num.sqrt (2%:R))%:C];
          [:: (1/Num.sqrt (2%:R))%:C; -(1/Num.sqrt (2%:R))%:C]]})%C.

Program Definition hadamard_gate := (@GateMixin 1 hadamard_matrix _ ).
Obligation 1.
  apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl; rewrite big_ord0; rewrite !mxE;
  destruct x as [[ | [ | x]] Hx]; destruct y as [[ | [ | y]] Hy]; simpl;
  try (absurd (x.+2 < 2)%N; auto); try (absurd (y.+2 < 2)%N; auto); rewrite addr0; rewrite !oppr0.
  rewrite mulr_real_complex. rewrite mulf_div. rewrite mulr1. rewrite -expr2. rewrite sqr_sqrtr; [|apply ler0n].
  rewrite addr_real_complex. rewrite addf_div; try (rewrite -unitfE; apply unitf_gt0; apply ltr0Sn).
  rewrite !mul1r. rewrite !mulr_natl. rewrite [2%:R *+ 2]mulr2n.
  rewrite divrr //; try (apply unitf_gt0; apply addr_gt0; apply ltr0Sn).

  rewrite mulrN. rewrite mulr_real_complex; rewrite mulf_div; rewrite mulr1; rewrite -expr2; rewrite sqr_sqrtr; [| apply ler0n].
  rewrite subr_real_complex. rewrite -mulNr. rewrite addf_div; try (rewrite -unitfE; apply unitf_gt0; apply ltr0Sn).
  rewrite mulNr. rewrite !mul1r. rewrite addrN. rewrite mul0r //.

  rewrite -mulNr; rewrite !mulr_real_complex; rewrite !mulf_div. rewrite !mulr1. rewrite -expr2. rewrite sqr_sqrtr; [| apply ler0n].
  rewrite addr_real_complex. rewrite addf_div; try (rewrite -unitfE; apply unitf_gt0; apply ltr0Sn).
  rewrite mulNr. rewrite mul1r. rewrite addrN. rewrite mul0r //.

  rewrite oppr_real_complex. rewrite -!mulNr. rewrite !mulr_real_complex. rewrite !mulf_div. rewrite mulNr. rewrite mulrN. rewrite opprK. rewrite mulr1. rewrite -expr2; rewrite sqr_sqrtr; [|apply ler0n].
  rewrite addr_real_complex; rewrite addf_div; try (rewrite -unitfE; apply unitf_gt0; apply ltr0Sn).
  rewrite !mul1r; rewrite !mulr_natl; rewrite [2%:R *+ 2]mulr2n.
  rewrite divrr //; try (apply unitf_gt0; apply addr_gt0; apply ltr0Sn).
Qed.

Definition select n (i: 'I_(2^n)) (bit: 'I_n) :=
  (i %% (2^(bit + 1)) >= 2^bit)%N.

Definition prob_0 n bit qubit :=
  \sum_(i < 2^n | ~~select i bit) `|(vector qubit) i 0| ^+ 2.

Definition prob_1 n bit qubit :=
  \sum_(i < 2^n | select i bit) `|(vector qubit) i 0| ^+ 2.

Definition measure_0 n (bit: 'I_n) (qubit: qubit_mixin_of n) :=
  if prob_0 bit qubit == 0
  then (vector qubit)
  else (\col_(i < 2^n)
     if ~~(select i bit)
     then (vector qubit) i 0 / sqrtc (prob_0 bit qubit)
     else 0).

Definition measure_1 n (bit: 'I_n) (qubit: qubit_mixin_of n) :=
  if prob_1 bit qubit == 0
  then (vector qubit)
  else (\col_(i < 2^n)
      if select i bit
      then (vector qubit) i 0 / sqrtc (prob_1 bit qubit)
      else 0).

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

Lemma measure0_unitary: forall n b q,
  \sum_(i < 2^n) `|(measure_0 b q) i 0|^+2 = 1.
Proof.
  move=> n b q. unfold measure_0. unfold prob_0.
  destruct (\sum_(i0 < 2^n | ~~select i0 b) `|(vector q) i0 0| ^+ 2 == 0) eqn:H.
    apply (vector_is_unit q).
    replace (\sum_(i < 2 ^ n) `|(\col_i0 _) i 0|^+2) with
      (\sum_(i < 2^n) (if ~~select i b then `|vector q i 0 / sqrtc (\sum_(i1 < 2 ^ n | ~~select i1 b) `|(vector q) i1 0| ^+2)| ^+ 2 else 0)).
      rewrite -!big_mkcond. apply measure_aux. rewrite unitfE. rewrite H //.
    apply eq_bigr; intros i _; rewrite mxE; destruct (~~select i b);
    [ reflexivity
    | auto; rewrite normr0; rewrite expr0n //
    ].
Qed.

Lemma measure1_unitary: forall n b q,
  \sum_(i < 2^n) `|(measure_1 b q) i 0|^+2 = 1.
Proof.
  move=> n b q. unfold measure_1. unfold prob_1.
  destruct (\sum_(i0 < 2^n | select i0 b) `|(vector q) i0 0| ^+ 2 == 0) eqn:H.
    apply (vector_is_unit q).
  replace (\sum_(i < 2 ^ n) `|(\col_i0 _) i 0|^+2) with
    (\sum_(i < 2^n) (if select i b then `|vector q i 0 / sqrtc (\sum_(i1 < 2 ^ n | select i1 b) `|(vector q) i1 0| ^+2)| ^+ 2 else 0)).
  rewrite -!big_mkcond. apply measure_aux. rewrite unitfE. rewrite H //.
  apply eq_bigr; intros i _; rewrite mxE; destruct (select i b);
  [ reflexivity
  | auto; rewrite normr0; rewrite expr0n //
  ].
Qed.

Program Definition measure_p (n: nat)  (i: 'I_n) (q: qubit_mixin_of n):
           list (R[i] * qubit_mixin_of n) :=
  [:: (prob_0 i q, (@QubitMixin n (measure_0 i q) _));
      (prob_1 i q, (@QubitMixin n (measure_1 i q) _))].
Obligation 1.
  intros n i q; apply measure0_unitary.
Qed.
Obligation 2.
  intros n i q; apply measure1_unitary.
Qed.

Program Definition cast (m: nat) (q: qubit_mixin_of m) (n: nat) (Heq: m = n): (qubit_mixin_of n) :=
  (@QubitMixin _ (castmx _ (vector q)) _).
Obligation 1.
  intros; split; try rewrite Heq; reflexivity.
Qed.
Obligation 2.
  intros. rewrite <- (vector_is_unit q). 
  assert (2^n = 2^m)%N. rewrite Heq; reflexivity.
  apply sum_cast with H.
    intros. rewrite castmxE. rewrite cast_ord_id. replace (cast_ord (esym (cast_obligation_1 Heq).1) x) with (cast_ord H x).
      reflexivity.
      unfold cast_ord.
      rewrite (eq_irrelevance (cast_ord_proof x H) (cast_ord_proof x (esym (cast_obligation_1 Heq).1))).
      reflexivity.
Qed.

Program Definition combine (n m: nat) (q1: qubit_mixin_of n) (q2: qubit_mixin_of m): (qubit_mixin_of (n+m)) :=
  (@QubitMixin _ (castmx _ (vector q1 *t vector q2)) _).
Obligation 1.
  intros n m q1 q2; split; [ symmetry; apply expnD | auto ].
Qed.
Obligation 2.
  intros n m q1 q2. simpl.
  replace (\sum_(i < 2^(n+m)) _) with
    (\sum_(i < 2^n * 2^m) `|(vector q1 *t vector q2) i 0| ^+ 2).
  transitivity (\sum_(i < 2^n*2^m) `|vector q1 (mxtens_unindex i).1 (mxtens_unindex (m:=1) (n:=1) 0).1| ^+ 2 * `|vector q2 (mxtens_unindex i).2 (mxtens_unindex (m:=1) (n:=1) 0).2| ^+ 2).
  apply eq_bigr; intros i _; rewrite mxE. rewrite normrM. rewrite exprMn //.
  destruct q1 as [q1 Hq1]; destruct q2 as [q2 Hq2].
  rewrite -(mulr_sum (fun x => `|q1 x (mxtens_unindex (m:=1) (n:=1) 0).1| ^+ 2) (fun x => `|q2 x (mxtens_unindex (m:=1) (n:=1) 0).2| ^+ 2)).
  rewrite sum_mul_dist. simpl.
  (* This can probably be done in a much easier way, but you know... *)
  replace (\sum_(j<2^m) `|q2 j _|^+2) with (1:R[i]).
  rewrite (eq_bigr _ (fun P x => mulr1 _)).
  replace (\sum_(i<2^n) `|q1 i _|^+2) with (1:R[i]). reflexivity.
    rewrite -Hq1. apply eq_bigr. intros i _. replace (q1 i 0) with (q1 i (Ordinal (mxtens_index_proof1 (m:=1) (n:=1) 0))).
      reflexivity. transitivity (q1 i (Ordinal (ltn0Sn 0))). replace (Ordinal (ltn0Sn 0)) with (Ordinal (mxtens_index_proof1 (m:=1) (n:=1) 0)).
      reflexivity. apply/val_eqP. simpl. auto.
      reflexivity.
    rewrite -Hq2. apply eq_bigr. intros i _. replace (q2 i 0) with (q2 i (Ordinal (mxtens_index_proof2 (m:=1) (n:=1) 0))).
      reflexivity. transitivity (q2 i (Ordinal (ltn0Sn 0))). replace (Ordinal (ltn0Sn 0)) with (Ordinal (mxtens_index_proof2 (m:=1) (n:=1) 0)).
      reflexivity. apply/val_eqP. simpl. auto.
      reflexivity.
  (* destruct combine_obligation_1.
  transitivity (\sum_(i < 2^(n+m)) `|(vector q1 *t vector q2) (cast_ord (sym_eq (combine_obligation_1 n m).1) i) 0| ^+ 2). *)
     apply sum_cast with (combine_obligation_1 n m).1. intros. rewrite castmxE. rewrite cast_ordK. rewrite cast_ord_id. reflexivity.
Qed.

Definition decomposable_aux (p: nat) (q: qubit_mixin_of p) (n m: nat) (Heq: (n + m = p)%N) :=
  exists (q1: qubit_mixin_of n) (q2: qubit_mixin_of m),
  (cast (combine q1 q2) Heq) = q.

Definition decomposable (p: nat) (q: qubit_mixin_of p) :=
  exists n m Heq, (@decomposable_aux p q n m Heq).

Definition entangled_aux (n: nat) (b1 b2: 'I_n) (q: qubit_mixin_of n) :=
  prob_0 b1 q <> (prob_0 b1 (QubitMixin (measure0_unitary b2 q)) + prob_0 b1 (QubitMixin (measure1_unitary b2 q))) \/
  prob_1 b1 q <> (prob_1 b1 (QubitMixin (measure0_unitary b2 q)) + prob_1 b1 (QubitMixin (measure1_unitary b2 q))).

Definition entangled n (q: qubit_mixin_of n) :=
  exists b1 b2, entangled_aux b1 b2 q.

Lemma znoits: (1 + 1 = 2)%N.
Proof.
  auto.
Qed.

Lemma dec_ind_2: forall (q: qubit_mixin_of 2),
  decomposable_aux q znoits
   <->
  prob_0 0 q = prob_0 0 (QubitMixin (measure0_unitary 1 q)) + prob_0 0 (QubitMixin (measure1_unitary 1 q)) /\
  prob_1 0 q = prob_1 0 (QubitMixin (measure0_unitary 1 q)) + prob_1 0 (QubitMixin (measure1_unitary 1 q)).
Proof.
  intros. unfold decomposable_aux; unfold combine; unfold cast; unfold measure_0; unfold measure_1;
  unfold prob_0; unfold prob_1; simpl; split.
    intros. destruct H as [q1 [q2 H]]. rewrite -H. clear H. simpl. split.
    repeat (rewrite !big_mkcond; rewrite !big_ord_recl; simpl; rewrite !big_ord0); rewrite !add0r; rewrite !addr0.
    assert ((castmx (cast_obligation_1 znoits)
     (eq_rect (2 ^ 1 * 2 ^ 1)%N ((matrix R[i])^~ (1 * 1)%N) (vector q1 *t vector q2) 
        (2 ^ (1 + 1))%N (combine_obligation_1 1 1))) ord0 0 =
     ((vector q1) 0 0) * ((vector q2) 0 0)).
       rewrite !castmxE. rewrite !cast_ord_id. 
       transitivity (((vector q1) *t (vector q2)) ord0 0). 
     unfold eq_rect. destruct (combine_obligation_1 1 1).
    cut ((castmx (cast_obligation_1 znoits)
     (eq_rect (2 ^ 1 * 2 ^ 1)%N ((matrix R[i])^~ (1 * 1)%N) (vector q1 *t vector q2) 
        (2 ^ (1 + 1))%N (combine_obligation_1 1 1))) (fintype.lift ord0 (fintype.lift ord0 ord0)) 0 =
      ((vector q1) 1 0) * ((vector q2) 0 0)).
     intros Teq2. rewrite Teq2.
    cut ((castmx (cast_obligation_1 znoits)
         (eq_rect (2 ^ 1 * 2 ^ 1)%N ((matrix R[i])^~ (1 * 1)%N) (vector q1 *t vector q2) 
            (2 ^ (1 + 1))%N (combine_obligation_1 1 1))) (fintype.lift ord0 ord0) 0 =
       ((vector q1) 0 0) * ((vector q2) 1 0)).
       intros Teq1. rewrite Teq1.
    
    rewrite !big_mkcond. rewrite !big_ord_recl. simpl. rewrite !big_ord0. rewrite !add0r.
    rewrite !big_mkcond. rewrite !big_ord_recl. simpl. rewrite !big_ord0. rewrite !add0r.
    rewrite !big_mkcond. rewrite !big_ord_recl. simpl. rewrite !big_ord0. rewrite !addr0.
 destruct (`|(castmx (cast_obligation_1 znoits)
         (eq_rect (2 ^ 1 * 2 ^ 1)%N ((matrix R[i])^~ (1 * 1)%N) (vector q1 *t vector q2) 
            (2 ^ (1 + 1))%N (combine_obligation_1 1 1))) ord0 0| ^+ 2 +
    `|(castmx (cast_obligation_1 znoits)
         (eq_rect (2 ^ 1 * 2 ^ 1)%N ((matrix R[i])^~ (1 * 1)%N) (vector q1 *t vector q2) 
            (2 ^ (1 + 1))%N (combine_obligation_1 1 1))) (fintype.lift ord0 ord0) 0| ^+ 2 == 0) eqn:X1.
   rewrite X1.
    rewrite !big_mkcond. rewrite !big_ord_recl. simpl. rewrite !big_ord0. rewrite !add0r.
    rewrite !big_mkcond. rewrite !big_ord_recl. simpl. rewrite !big_ord0. rewrite !add0r. rewrite !addr0.
    rewrite X1.
(* we hope to prove this, of course
Theorem decomposable_entangled: forall n (q: qubit_mixin_of n), ~decomposable q <-> entangled q.
Proof.
  intros. unfold decomposable; unfold decomposable_aux; unfold combine; unfold cast;
    unfold entangled; unfold entangled_aux; unfold measure_0; unfold measure_1; unfold prob_0; unfold prob_1.
  simpl.
  split.
    intros. destruct H. [m1 [m2 [Heq [q1 [q2 H]]]]]. rewrite <- H. clear H. simpl.*)

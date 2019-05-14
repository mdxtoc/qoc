(* Main quantum library *)

From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Num.Theory GRing.Theory ComplexField.

Require Import other_stuff complex_stuff.

Section QubitVectorDef.

Variable n: nat.

(* The qubit datatype, parametrised by the length of the vector and a proof that it is a unit vector.
 * (qubit_vector_of n) is therefore the type of n-qubit vectors. *)
Structure qubit_vector_of := QubitVector {
  vector:> 'cV[complex_stuff.R [i]]_(2 ^ n);
  vector_is_unit: \sum_(i < 2^n) `|vector i 0| ^+ 2 == 1
}.

Canonical qubit_vector_subType := Eval hnf in [subType for vector].

Implicit Type qv: qubit_vector_of.

Definition qubit_vector qv mkQV : qubit_vector_of :=
  mkQV (let: QubitVector _ qvP := qv return \sum_(i < 2^n) `|qv i 0|^+2 == 1 in qvP).

Lemma qubit_vectorE qv : qubit_vector (fun qvP => @QubitVector qv qvP) = qv.
Proof.
  by case: qv.
Qed.

End QubitVectorDef.

Lemma zero_qubitP: \sum_(i < 2^0) `|((1:R[i])%:M) i 0| ^+ 2 == 1.
Proof.
  by rewrite big_ord1; rewrite mxE; rewrite normc_def; rewrite expr1n; rewrite expr0n; rewrite addr0; rewrite sqrtr1; rewrite expr1n.
Qed.
Canonical zero_qubit := QubitVector zero_qubitP.

Section GateDef.

Variable n: nat.

(* The gate datatype, paramtetrised by its size (number of inputs) and proof that it is a unitary matrix *)
Structure gate_of := Gate {
  matrix:> 'M[complex_stuff.R [i]]_(2 ^ n);
  matrix_is_unitary: unitarymx matrix
}.

Canonical matrix_subType := Eval hnf in [subType for matrix].

Implicit Type g: gate_of.

Definition gate g mkG : gate_of :=
  mkG (let: Gate _ gP := g return unitarymx g in gP).

Lemma gateE g : gate (fun gP => @Gate g gP) = g.
Proof.
  by case: g.
Qed.

End GateDef.

(* The apply operator; (apply q g) applies gate g to qubit vector q.
 * Needs proof that this results in a new qubit, which is by using the fact that gates are unitary matrices. *)
Lemma applyP: forall n g q,
  \sum_(i < 2^n) `|(matrix g *m vector q) i 0| ^+ 2 == 1.
  intros n g q; destruct q as [q Hq]; destruct g as [g Hg]; simpl;
  rewrite -conjugate_is_sum; rewrite -unitary_preserves_product;
  [ rewrite mxE; rewrite -(eqP Hq); apply/eqP; apply eq_bigr; intros i _;
    rewrite mulrC; rewrite !mxE; symmetry; apply sqr_normc
  | apply Hg
  ].
Qed.
Canonical apply n g q := (@QubitVector n _ (applyP g q)).

Lemma I_gateP: (@unitarymx 2 'M{[:: [:: 1; 0]; [:: 0; 1]]}).
  unfold unitarymx; apply/eqP; apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl;
  rewrite big_ord0. rewrite !mxE; simpl. 
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
  ];
  simpl; try repeat (rewrite mulr0 || rewrite mul0r || rewrite addr0 || rewrite add0r || rewrite mul1r || rewrite mulr1);
  rewrite oppr0 //.
Qed.
Canonical I_gate := (@Gate 1 _ I_gateP).

(* Definition of the X gate *)
Lemma X_gateP: (@unitarymx 2 'M{[:: [:: 0; 1]; [:: 1; 0]]}).
Proof.
  apply/eqP. apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl; rewrite big_ord0; rewrite !mxE;
  destruct x as [[ | [ | x]] Hx]; destruct y as [[ | [ | y]] Hy]; simpl;
  try (absurd (x.+2 < 2)%N; auto); try (absurd (y.+2 < 2)%N; auto);
  try repeat (rewrite mul0r || rewrite mulr0 || rewrite mulr1 || rewrite addr0 || rewrite add0r || rewrite oppr0 || rewrite mulNr || rewrite mulrN);
  auto.
Qed.
Canonical X_gate := (@Gate 1 _ X_gateP).

(* Definition of the Y gate *)
Lemma Y_gateP: (@unitarymx 2 'M{[:: [:: 0; -'i]; [:: 'i; 0]]}).
Proof.
  apply/eqP. apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl; rewrite big_ord0; rewrite !mxE;
  destruct x as [[ | [ | x]] Hx]; destruct y as [[ | [ | y]] Hy]; simpl;
  try (absurd (x.+2 < 2)%N; auto); try (absurd (y.+2 < 2)%N; auto);
  try repeat (rewrite mul0r || rewrite mulr0 || rewrite mulr1 || rewrite addr0 || rewrite add0r || rewrite oppr0 || rewrite mulNr || rewrite mulrN || rewrite opprK || rewrite -expr2 || rewrite sqr_i || rewrite complex_minus_i);
  auto.
Qed.
Canonical Y_gate := (@Gate 1 _ Y_gateP).

(* Definition of the Z gate *)
Lemma Z_gateP: (@unitarymx 2 'M{[:: [:: 1; 0]; [:: 0; -1]]}).
Proof.
  apply/eqP; apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl; rewrite big_ord0; rewrite !mxE;
  destruct x as [[ | [ | x]] Hx]; destruct y as [[ | [ | y]] Hy]; simpl;
  try (absurd (x.+2 < 2)%N; auto); try (absurd (y.+2 < 2)%N; auto);
  try repeat (rewrite mul0r || rewrite mulr0 || rewrite mulr1 || rewrite addr0 || rewrite add0r || rewrite oppr0 || rewrite mulNr || rewrite mulrN);
  auto;
  rewrite -oppr0; unfold GRing.opp; simpl; rewrite !opprK //.
Qed.
Canonical Z_gate := (@Gate 1 _ Z_gateP).

(* Definition of the Hadamard gate *)
Lemma hadamard_gateP: (@unitarymx 2 'M{[:: [:: (1/Num.sqrt (2%:R))%:C; (1/Num.sqrt (2%:R))%:C];
          [:: (1/Num.sqrt (2%:R))%:C; -(1/Num.sqrt (2%:R))%:C]]})%C.
Proof.
  apply/eqP; apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl; rewrite big_ord0; rewrite !mxE;
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
Canonical hadamard_gate := (@Gate 1 _ hadamard_gateP).

(* Definition of the Cnot gate *)
Lemma cnot_gateP: (@unitarymx 4 'M{[:: [:: 1; 0; 0; 0]; [:: 0; 1; 0; 0]; [:: 0; 0; 0; 1]; [:: 0; 0; 1; 0]]}).
Proof.
  apply/eqP; apply/matrixP; intros x y; rewrite !mxE; rewrite !big_ord_recl; rewrite big_ord0; rewrite !mxE.
  destruct x as [[ | [ | [ | [ | x]]]] Hx]; destruct y as [[ | [ | [ | [ | y]]]] Hy]; simpl;
  try (absurd (x.+4 < 4)%N; auto); try (absurd (y.+4 < 4)%N; auto);  
  try repeat (rewrite !mulr0 || rewrite !mul0r || rewrite !addr0 || rewrite !add0r || rewrite !mulr1 || rewrite !oppr0 || reflexivity).
Qed.
Canonical cnot_gate := (@Gate 2 _ cnot_gateP).

(* Here we begin the definitions pertaining to measurement. *)

(* A binary predicate to select the parts of a qubit vector that represent a specific qubit measuring as 1.
   In a 3-qubit vector, which has 8 elements, the elements represent P(|000>), P(|001>), P(|010>), ..., P(|111>).
   Therefore, the elements representing bit 1 (counting from 0) measuring as 1 are elements 2, 3, 6 and 7
   (if we start counting at 0).
   i.e. the elements n where n modulo 4 is 2 or 3 *) 
Definition select n (i: 'I_(2^n)) (bit: 'I_n) :=
  (i %% (2^(bit + 1)) >= 2^bit)%N.

(* The probabilities that qubit b of qubit vector q measures as 0 or 1 respectively. *)

Local Open Scope complex_scope.
Definition prob_0 {n} b q: R :=
  \sum_(i < 2^n | ~~select i b) (normc ((vector q) i 0)) ^+ 2.

Definition prob_1 {n} b q: R :=
  \sum_(i < 2^n | select i b) (normc ((vector q) i 0)) ^+ 2.

(* The new qubit vectors that result after measuring bit b of qubit vector q and getting 0 or 1 respectively. *)
Definition measure_0 n (b: 'I_n) (q: qubit_vector_of n) :=
  if prob_0 b q == 0
  then (vector q)
  else (\col_(i < 2^n)
     if ~~(select i b)
     then (vector q) i 0 / sqrtc (prob_0 b q)%:C
     else 0).

Definition measure_1 n (b: 'I_n) (q: qubit_vector_of n) :=
  if prob_1 b q == 0
  then (vector q)
  else (\col_(i < 2^n)
      if select i b
      then (vector q) i 0 / sqrtc (prob_1 b q)%:C
      else 0).

(* The proofs that these new vectors are unitary. *)
Lemma measure_aux: forall I (r: seq I) P (F: I -> R[i]), 
  (\sum_(i <- r | P i) `|F i|^+2) \is a GRing.unit ->
  \sum_(i <- r | P i) (`|F i / sqrtc (\sum_(i <- r | P i) `|F i|^+2)|^+2) == 1.
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
        [ rewrite divrr //; apply H
        | apply addr_ge0; [ apply exprn_ge0; apply normr_ge0 | apply sumr_ge0; intros x _; apply exprn_ge0; apply normr_ge0 ]
        ]
      | apply eq_bigr; intros x _; rewrite Num.Theory.normf_div; rewrite expr_div_n //
      ]
    | replace (\sum_(j <- r | P j) `|F j / sqrtc _| ^+ 2) with
      (\sum_(j <- r | P j) `|F j|^+2 / `|sqrtc (\sum_(j0 <- r | P j0) `|F j0|^+2)|^+2);
      [ rewrite -mulr_suml; rewrite sqrtc_norm;
        [ rewrite divrr //; apply H
        | apply sumr_ge0; intros x _; apply exprn_ge0; apply normr_ge0
        ]
      | apply eq_bigr; intros x _; rewrite normf_div; rewrite expr_div_n //
      ]
    ]
  ].
Qed.

Lemma blerp3: forall x: R,
  x%:C = 0 -> x = 0.
Proof. 
  intros. transitivity (complex.Re (x%:C)).
    auto.
    assert (x%:C == 0). apply/eqP. apply H.
    rewrite (eq_complex x%:C 0) in H0. 
    destruct (proj1 (andP _ _) H0).
    rewrite H. auto.
Qed.

Lemma measure0_unitary: forall n b q,  \sum_(i < 2^n) `|(measure_0 b q) i 0|^+2 == 1.
Proof.
  move=> n b q. unfold measure_0. unfold prob_0.
  destruct (\sum_(i0 < 2^n | ~~select i0 b) (normc ((vector q) i0 0)) ^+ 2 == 0) eqn:H.
    rewrite H; apply (vector_is_unit q).
    rewrite H. replace (\sum_(i < 2 ^ n) `|(\col_i0 _) i 0|^+2) with
      (\sum_(i < 2^n) (if ~~select i b then `|vector q i 0 / sqrtc (\sum_(i1 < 2 ^ n | ~~select i1 b) `|(vector q) i1 0| ^+2)| ^+ 2 else 0)).
    rewrite -!big_mkcond. apply measure_aux. rewrite unitfE.   
    assert ((\sum_(i < 2^n | ~~select i b) (normc ((vector q) i 0)) ^+ 2)%:C = 
       \sum_(i < 2^n | ~~select i b) `|q i 0| ^+ 2).
      rewrite -rcsum. apply eq_bigr. intros. rewrite normc_equiv. rewrite !expr2. simpc. reflexivity.
    rewrite -H0. apply/eqP. intro. 
    apply Bool.eq_true_false_abs with (\sum_(i0 < 2^n|~~select i0 b) normc (q i0 0) ^+ 2 == 0).
    apply/eqP. apply blerp3. apply H1. apply H.
    apply eq_bigr. intros i _. rewrite mxE.
    destruct (~~select i b).
       repeat f_equal. rewrite -rcsum. apply eq_bigr. intros. (* here *)
       rewrite normc_equiv. rewrite !real_complexE. rewrite !expr2. simpc. reflexivity.
    auto; rewrite normr0; rewrite expr0n //.
Qed.

Lemma measure1_unitary: forall n b q,
  \sum_(i < 2^n) `|(measure_1 b q) i 0|^+2 == 1.
Proof.
  move=> n b q. unfold measure_1. unfold prob_1.
  destruct (\sum_(i0 < 2^n | select i0 b) (normc ((vector q) i0 0)) ^+ 2 == 0) eqn:H.
    rewrite H; apply (vector_is_unit q).
    rewrite H; replace (\sum_(i < 2 ^ n) `|(\col_i0 _) i 0|^+2) with
    (\sum_(i < 2^n) (if select i b then `|vector q i 0 / sqrtc (\sum_(i1 < 2 ^ n | select i1 b) `|(vector q) i1 0| ^+2)| ^+ 2 else 0)).
  rewrite -!big_mkcond. apply measure_aux. rewrite unitfE.
  assert ((\sum_(i < 2^n | select i b) (normc ((vector q) i 0)) ^+ 2)%:C = 
       \sum_(i < 2^n | select i b) `|q i 0| ^+ 2).
    rewrite -rcsum. apply eq_bigr. intros. rewrite normc_equiv. rewrite !expr2. simpc. reflexivity.
    rewrite -H0. apply/eqP. intro. 
    apply Bool.eq_true_false_abs with (\sum_(i0 < 2^n|select i0 b) normc (q i0 0) ^+ 2 == 0).
    apply/eqP. apply blerp3. apply H1. apply H.
  apply eq_bigr; intros i _; rewrite mxE; destruct (select i b);
  [ repeat f_equal; rewrite -rcsum; apply eq_bigr; intros;
    rewrite normc_equiv; rewrite !real_complexE; rewrite !expr2; simpc; reflexivity
  | auto; rewrite normr0; rewrite expr0n //
  ].
Qed.

(* The measure function. measure_p b q returns a tuple of two pairs; the first element of each pair is the
 * probability that bit b of qubit vector q is 0 or 1 respectively; the second element of each pair is the
 * new qubit vector that results in each case. *)
Definition measure_p (n: nat)  (b: 'I_n) (q: qubit_vector_of n):
           (R * qubit_vector_of n) * (R * qubit_vector_of n) :=
  ((prob_0 b q, (QubitVector (measure0_unitary b q))),
   (prob_1 b q, (QubitVector (measure1_unitary b q)))).

(* Qubit vector casting. If m = n, then the datatypes (qubit_vector m) and (qubit_vector n) are interchangeable. *)
Lemma castP:
  forall m q n (Heq: m = n), \sum_(i < 2^n) `|(castmx (f_equal (expn 2) Heq, (eq_S 0 0 (eqP (eq_refl 0)))%N) (vector q)) i 0| ^+ 2 == 1.
Proof.
  intros. rewrite <- (eqP (vector_is_unit q)).
  apply/eqP. apply sum_cast with (f_equal (expn 2) (sym_eq Heq)).
    auto.
    intros. rewrite castmxE. rewrite cast_ord_id.
      unfold cast_ord. repeat f_equal. apply eq_irrelevance.
Qed.
Canonical cast m q n Heq := (@QubitVector n _ (@castP m q n Heq)).

Lemma cast_id: forall n (h: qubit_vector_of n) (Heq: n = n),
  cast h Heq = h.
Proof.
  intros; destruct h as [h Hh]. unfold cast. apply val_inj; simpl; apply castmx_id.
Qed.

Lemma cast_irrelevance: forall n (h: qubit_vector_of n) n' (H1 H2: n = n'),
  cast h H1 = cast h H2.
Proof.
  intros. apply val_inj; simpl. apply/matrixP. intros i j. rewrite !castmxE. unfold cast_ord. simpl.
  rewrite (ordinal_eq (cast_ord_proof i (esym (f_equal (expn 2) H1))) (cast_ord_proof i (esym (f_equal (expn 2) H2)))).
    reflexivity. reflexivity.
Qed.

(* Qubit vector combination. An m-qubit vector and an n-qubit vector can be combined (by taking their tensor
 * product) into an m+n-qubit vector. *)
Lemma combineP:
  forall m n q1 q2, \sum_(i < 2^(m+n)) `|(castmx (sym_eq (expnD 2 m n), (eq_S 0 0 (eqP (eq_refl 0)))%N) (vector q1 *t vector q2)) i 0| ^+ 2 == 1.
Proof.
  intros m n q1 q2. apply/eqP.
  replace (\sum_(i < 2^(m+n)) _) with
    (\sum_(i < 2^m * 2^n) `|(vector q1 *t vector q2) i 0| ^+ 2).
  transitivity (\sum_(i < 2^m*2^n) `|vector q1 (mxtens_unindex i).1 (mxtens_unindex (m:=1) (n:=1) 0).1| ^+ 2 * `|vector q2 (mxtens_unindex i).2 (mxtens_unindex (m:=1) (n:=1) 0).2| ^+ 2).
  apply eq_bigr; intros i _; rewrite mxE. rewrite normrM. rewrite exprMn //.
  destruct q1 as [q1 Hq1]; destruct q2 as [q2 Hq2].
  rewrite -(mulr_sum (fun x => `|q1 x (mxtens_unindex (m:=1) (n:=1) 0).1| ^+ 2) (fun x => `|q2 x (mxtens_unindex (m:=1) (n:=1) 0).2| ^+ 2)).
  rewrite sum_mul_dist. simpl.
  (* This can probably be done in a much easier way, but you know... *)
  replace (\sum_(j<2^n) `|q2 j _|^+2) with (1:R[i]).
  rewrite (eq_bigr _ (fun P x => mulr1 _)).
  replace (\sum_(i<2^m) `|q1 i _|^+2) with (1:R[i]). reflexivity.
    rewrite -(eqP Hq1). apply eq_bigr. intros i _. replace (q1 i 0) with (q1 i (Ordinal (mxtens_index_proof1 (m:=1) (n:=1) 0))).
      reflexivity. transitivity (q1 i (Ordinal (ltn0Sn 0))). replace (Ordinal (ltn0Sn 0)) with (Ordinal (mxtens_index_proof1 (m:=1) (n:=1) 0)).
      reflexivity. apply/val_eqP. simpl. auto.
      reflexivity.
    rewrite -(eqP Hq2). apply eq_bigr. intros i _. replace (q2 i 0) with (q2 i (Ordinal (mxtens_index_proof2 (m:=1) (n:=1) 0))).
      reflexivity. transitivity (q2 i (Ordinal (ltn0Sn 0))). replace (Ordinal (ltn0Sn 0)) with (Ordinal (mxtens_index_proof2 (m:=1) (n:=1) 0)).
      reflexivity. apply/val_eqP. simpl. auto.
      reflexivity.
    apply sum_cast with (sym_eq (expnD 2 m n)). auto. intros. rewrite castmxE. rewrite cast_ordK. rewrite cast_ord_id. reflexivity.
Qed.
Canonical combine m n q1 q2 := (@QubitVector (m+n) _ (@combineP m n q1 q2)).

Lemma combine0q: forall n, left_id zero_qubit (@combine 0 n).
Proof.
  intros n x; destruct x as [x Hx]; unfold combine.
  apply val_inj. simpl. rewrite tens_scalar1mx. rewrite castmx_comp. apply/matrixP.
  intros i j. rewrite !castmxE. simpl; f_equal; apply cast_ord_id.
Qed.

Lemma combineq0: forall n q, (@combine n 0 q zero_qubit) = (cast q (sym_eq (addn0 n))).
Proof.
  intros n x; destruct x as [x Hx]; unfold cast; unfold combine.
  apply val_inj; simpl. rewrite tens_mx_scalar. rewrite castmx_comp. apply/matrixP.
  intros i j. rewrite !castmxE. simpl. rewrite scale1r. f_equal; unfold cast_ord; f_equal; apply eq_irrelevance.
Qed.

Lemma combineA: forall m n k (h: qubit_vector_of m) (h': qubit_vector_of n) (q: qubit_vector_of k) H,
 cast (combine (combine h h') q) H = combine h (combine h' q).
Proof.
  intros. apply val_inj; simpl. rewrite !castmx_comp. apply/matrixP. intros i j. rewrite !castmxE.
  rewrite !mxE. rewrite !castmxE. rewrite !mxE. simpl. rewrite mulrA. f_equal. f_equal.
    rewrite (ordinal_eq (mxtens_index_proof1 (cast_ord (esym (Logic.eq_sym (expnD 2 m n)))
           (Ordinal
              (mxtens_index_proof1
                 (cast_ord (esym (etrans (Logic.eq_sym (expnD 2 (m + n) k)) (f_equal (expn 2) H))) i)))))
      (mxtens_index_proof1 (cast_ord (esym (Logic.eq_sym (expnD 2 m (n + k)))) i))).
    rewrite (ordinal_eq 
       (@mxtens_index_proof1 1 1
        (@cast_ord 1 1 (@esym nat 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0))))%N
           (@Ordinal 1 (j %/ 1)
              (@mxtens_index_proof1 1 1
                 (@cast_ord 1 1
                    (@esym nat 1 1
                       (@etrans nat 1 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0)))
                          (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0)))))%N j)))))
       (@mxtens_index_proof1 1 1 (@cast_ord 1 1 (@esym nat 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0))))%N j))).
    reflexivity.
      rewrite divn1 //.
      simpl. rewrite -divnMA. rewrite (mulnC (2^k) (2^n))%N. rewrite (expnD 2 n k). reflexivity. 
    rewrite (ordinal_eq (mxtens_index_proof2
        (cast_ord (esym (Logic.eq_sym (expnD 2 m n)))
           (Ordinal
              (mxtens_index_proof1
                 (cast_ord (esym (etrans (Logic.eq_sym (expnD 2 (m + n) k)) (f_equal (expn 2) H))) i)))))
      (mxtens_index_proof1
        (cast_ord (esym (Logic.eq_sym (expnD 2 n k)))
           (Ordinal (mxtens_index_proof2 (cast_ord (esym (Logic.eq_sym (expnD 2 m (n + k)))) i)))))).
    rewrite (ordinal_eq (@mxtens_index_proof2 1 1
        (@cast_ord 1 1 (@esym nat 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0))))%N
           (@Ordinal 1 (j %/ 1)
              (@mxtens_index_proof1 1 1
                 (@cast_ord 1 1
                    (@esym nat 1 1
                       (@etrans nat 1 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0)))
                          (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0)))))%N j)))))
     (@mxtens_index_proof1 1 1
        (@cast_ord 1 1 (@esym nat 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0))))%N
           (@Ordinal 1 (j %% 1)
              (@mxtens_index_proof2 1 1
                 (@cast_ord 1 1 (@esym nat 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0))))%N j)))))).
      reflexivity.
        simpl. rewrite !divn1 //.
        simpl. rewrite (expnD 2 n k). rewrite !modn_def. case: edivnP => p r. case: edivnP => p' r'. simpl. intros.
          rewrite e in e0. rewrite mulnA in e0. rewrite divnMDl in e0. symmetry. apply (blerp e0).
          rewrite ltn_divLR. apply (implP i0). rewrite muln_gt0. apply <- andP. split. 
            rewrite expn_gt0. apply orP. left; auto.
            rewrite expn_gt0. apply orP. left; auto.
            rewrite expn_gt0. apply orP. left; auto.
            apply (implP i1).            rewrite expn_gt0. apply orP. left; auto.
            rewrite expn_gt0. apply orP. left; auto.
  rewrite (ordinal_eq (mxtens_index_proof2 (cast_ord (esym (etrans (Logic.eq_sym (expnD 2 (m + n) k)) (f_equal (expn 2) H))) i))
   (mxtens_index_proof2
        (cast_ord (esym (Logic.eq_sym (expnD 2 n k)))
           (Ordinal (mxtens_index_proof2 (cast_ord (esym (Logic.eq_sym (expnD 2 m (n + k)))) i)))))).
  rewrite (ordinal_eq (@mxtens_index_proof2 1 1
        (@cast_ord 1 1
           (@esym nat 1 1
              (@etrans nat 1 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0)))
                 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0)))))%N j))
(@mxtens_index_proof2 1 1
        (@cast_ord 1 1 (@esym nat 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0))))%N
           (@Ordinal 1 (j %% 1)
              (@mxtens_index_proof2 1 1
                 (@cast_ord 1 1 (@esym nat 1 1 (eq_S 0 0 ((@eqP nat_eqType 0 0) (eqxx 0))))%N j)))))).
    reflexivity.
       simpl. rewrite !modn1 //.
       simpl. rewrite (expnD 2 n k). symmetry. apply modn_dvdm. apply dvdn_mull. apply dvdnn.
Qed.

Lemma blerp2: forall n k: nat, (k = 0 -> n = n + k)%N.
Proof.
  intros. rewrite H. symmetry. apply addn0.
Qed.
Lemma gnarf: forall n k k', k = k'.+1 -> (n + 1 + k' = n + k)%N.
Proof.
  intros. rewrite H. rewrite (addnS n k'). rewrite addnAC. rewrite addn1 //.
Qed.
Lemma znoits: forall k k', k = k'.+1 -> k.-1 = k'.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Check castmx_comp.
(* Combine a list of k 1-qubit vectors into one k-qubit vector. We use the 0-qubit vector as an initial value
   here, as it is the neutral element of the tensor product. *)
Fixpoint combine_tuple_aux (n: nat) (q: qubit_vector_of n) (k: nat) (l: k .-tuple (qubit_vector_of 1)) { struct k }: (qubit_vector_of (n+k)) :=
  (match k as m return (k = m) -> _ with
  | 0     => fun H: (k = 0)%N =>
             cast q (blerp2 n H)
  | k'.+1 => fun H: k = k'.+1 =>
             cast (combine_tuple_aux (combine q (thead (tcast H l))) (tcast (znoits H) (behead_tuple l))) (gnarf n H)
  end) (Logic.eq_refl k).


Definition combine_tuple (k: nat) (l: k.-tuple (qubit_vector_of 1)): (qubit_vector_of k) :=
  (combine_tuple_aux zero_qubit l).

Lemma combine_tuple_rec: forall (k: nat) (n: nat) (h: qubit_vector_of n) (t: k.-tuple (qubit_vector_of 1)),
  combine_tuple_aux h t = combine h (combine_tuple t).
Proof.
  intros. unfold combine_tuple. generalize n h; clear n h; induction k; intros n h;
  [ simpl; rewrite !cast_id; rewrite combineq0; f_equal; apply eq_irrelevance
  |
  ].
  simpl. rewrite !cast_id. rewrite !tcast_id. generalize t; clear t; case/tupleP. intros h' t.
    rewrite !theadE. rewrite behead_tupleE. rewrite combine0q.
    rewrite IHk. rewrite IHk. rewrite combine0q. rewrite (IHk [tuple of t] (1%N) h').
    rewrite -(combineA h h'). apply cast_irrelevance.
Qed. 

(*Lemma combine_tupleE: forall k (l: k.-tuple (qubit_vector_of 1)) i,
  vector (combine_tuple l) i 0 =
  \prod_(n < k) (vector (tnth l n)) (if (select i n) then 1 else 0) 0. *)

(* Definition of decomposability. A qubit vector is decomposable if it can be written as the combination of
 * two qubit vectors. It is maximally decomposable if it can be written as a combination of 1-qubit vectors. *)
Definition decomposable_aux (p: nat) (q: qubit_vector_of p) (n m: nat) (Heq: (n + m = p)%N) :=
  exists (q1: qubit_vector_of n) (q2: qubit_vector_of m),
  (cast (combine q1 q2) Heq) = q.

Definition decomposable (p: nat) (q: qubit_vector_of p) :=
  exists n m Heq, (@decomposable_aux p q n m Heq).

Definition maximally_decomposable (n: nat) (q: qubit_vector_of n) :=
  exists (l: n.-tuple (qubit_vector_of 1)), combine_tuple l = q.

(* Definition of entanglement. A qubit vector is entangled if there are two qubits b1 and b2 such that measuring
 * b1 influences the probability distribution of measuring b2. It is maximally entangled if all qubits in the
 * vector influence each other. It is disentangled if no qubits in the vector influence each other. *)
Definition disentangled_aux (n: nat) (b1 b2: 'I_n) (q: qubit_vector_of n) :=
  prob_0 b1 (QubitVector (measure0_unitary b2 q)) = prob_0 b1 (QubitVector (measure1_unitary b2 q)) /\
  prob_1 b1 (QubitVector (measure0_unitary b2 q)) = prob_1 b1 (QubitVector (measure1_unitary b2 q)).

Definition disentangled (n: nat) (q: qubit_vector_of n) :=
  forall b1 b2, disentangled_aux b1 b2 q.

Definition maximally_entangled (n: nat) (q: qubit_vector_of n) :=
  forall b1 b2, ~disentangled_aux b1 b2 q.

Lemma frob:
  forall n q b, ~(\sum_(i < 2^n | ~~select i b) `|(vector q) i 0| ^+2 == 0 /\
                  \sum_(i < 2^n | select i b) `|(vector q) i 0| ^+ 2 == 0).
Proof.
  intros. intro X. destruct X. 
  absurd ((GRing.one (ComplexField.complex_numDomainType R)) == 0 + 0).
    intro. rewrite add0r in H1. rewrite oner_eq0 in H1. inversion H1.
  rewrite -{1}(eqP H). rewrite -{2}(eqP H0).
  rewrite sum_if_not. apply/eqP. symmetry. apply/eqP. apply (vector_is_unit q).
Qed.

(* Entanglement and decomposability are equivalent. *)
(* Theorem decdis n (q: qubit_vector_of n):
  maximally_decomposable q -> disentangled q. *)

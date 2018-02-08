(* Main quantum library *)

From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Num.Theory GRing.Theory.

Require Import other_stuff complex_stuff.

(* The qubit datatype, parametrised by the length of the vector and a proof that it is a unit vector.
 * (qubit_vector_of n) is therefore the type of n-qubit vectors. *)
Record qubit_vector_of (n: nat) := QubitVectorMixin {
  vector: 'cV[complex_stuff.R [i]]_(2 ^ n);
  vector_is_unit: \sum_(i < 2^n) `|vector i 0|^+2 = 1
}.

(* A putative 0-qubit vector, which we need for initial values sometimes.
 * Reasoning down from the 1-qubit vector, this is a 1x1 unit matrix. *)
Program Definition zero_qubit: (qubit_vector_of 0) :=
  (@QubitVectorMixin 0 (1%:M) _).
Obligation 1.
  rewrite big_ord1. rewrite mxE. rewrite normc_def. rewrite expr1n. rewrite expr0n. rewrite addr0. rewrite sqrtr1. rewrite expr1n //.
Qed.

(* The gate datatype, paramtetrised by its size (number of inputs) and proof that it is a unitary matrix *)
Record gate_mixin_of (n: nat): Type := GateMixin {
  gate: 'M[complex_stuff.R [i]]_(2 ^ n);
  gate_is_unitary: unitarymx gate
}.

(* The apply operator; (apply q g) applies gate g to qubit vector q.
 * Needs proof that this results in a new qubit, which is by using the fact that gates are unitary matrices. *)
Program Definition apply (n: nat) (q: qubit_vector_of n) (g:gate_mixin_of n): qubit_vector_of n :=
  (@QubitVectorMixin _ (gate g *m vector q) _).
Obligation 1.
  intros n q g; destruct q as [q Hq]; destruct g as [g Hg]; simpl.
  rewrite -conjugate_is_sum. rewrite -unitary_preserves_product;
  [ rewrite !mxE; rewrite -Hq; apply eq_bigr; intros i _;
    rewrite mulrC; rewrite !mxE; symmetry; apply sqr_normc
  | apply Hg
  ]. 
Qed.

(* Definition of the matrix that forms the I gate *)
Definition I_matrix: 'M[R [i]]_2 :=
  'M{[:: [:: 1; 0];
         [:: 0; 1]]}.

(* The I gate (which needs a proof that the I matrix is unitary *)
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

(* Definition of the X gate *)
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

(* Definition of the Y gate *)
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

(* Definition of the Z gate *)
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

(* Definition of the Hadamard gate *)
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

(* Here we begin the definitions pertaining to measurement. *)

(* A binary predicate to select the parts of a qubit vector that represent a specific qubit measuring as 1.
   In a 3-qubit vector, which has 8 elements, the elements represent P(|000>), P(|001>), P(|010>), ..., P(|111>).
   Therefore, the elements representing bit 1 (counting from 0) measuring as 1 are elements 2, 3, 6 and 7
   (if we start counting at 0).
   i.e. the elements n where n modulo 4 is 2 or 3 *) 
Definition select n (i: 'I_(2^n)) (bit: 'I_n) :=
  (i %% (2^(bit + 1)) >= 2^bit)%N.

(* The probabilities that qubit b of qubit vector q measures as 0 or 1 respectively. *)
Definition prob_0 n b q :=
  \sum_(i < 2^n | ~~select i b) `|(vector q) i 0| ^+ 2.

Definition prob_1 n b q :=
  \sum_(i < 2^n | select i b) `|(vector q) i 0| ^+ 2.

(* The new qubit vectors that result after measuring bit b of qubit vector q and getting 0 or 1 respectively. *)
Definition measure_0 n (b: 'I_n) (q: qubit_vector_of n) :=
  if prob_0 b q == 0
  then (vector q)
  else (\col_(i < 2^n)
     if ~~(select i b)
     then (vector q) i 0 / sqrtc (prob_0 b q)
     else 0).

Definition measure_1 n (b: 'I_n) (q: qubit_vector_of n) :=
  if prob_1 b q == 0
  then (vector q)
  else (\col_(i < 2^n)
      if select i b
      then (vector q) i 0 / sqrtc (prob_1 b q)
      else 0).

(* The proofs that these new vectors are unitary. *)
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

(* The measure function. measure_p b q returns a list of two pairs; the first element of each pair is the
 * probability that bit b of qubit vector q is 0 or 1 respectively; the second element of each pair is the
 * new qubit vector that results in each case. *)
Definition measure_p (n: nat)  (b: 'I_n) (q: qubit_vector_of n):
           list (R[i] * qubit_vector_of n) :=
  [:: (prob_0 b q, (QubitVectorMixin (measure0_unitary b q)));
      (prob_1 b q, (QubitVectorMixin (measure1_unitary b q)))].

(* Qubit vector casting. If m = n, then the datatypes (qubit_vector m) and (qubit_vector n) are interchangeable. *)
Program Definition cast (m: nat) (q: qubit_vector_of m) (n: nat) (Heq: m = n): (qubit_vector_of n) :=
  (@QubitVectorMixin _ (castmx _ (vector q)) _).
Obligation 1.
  intros; split; try rewrite Heq; reflexivity.
Qed.
Obligation 2.
  intros. rewrite <- (vector_is_unit q). 
  assert (2^n = 2^m)%N. rewrite Heq; reflexivity.
  apply sum_cast with H.
    auto.
    intros. rewrite castmxE. rewrite cast_ord_id. replace (cast_ord (esym (cast_obligation_1 Heq).1) x) with (cast_ord H x).
      reflexivity.
      unfold cast_ord.
      rewrite (eq_irrelevance (cast_ord_proof x H) (cast_ord_proof x (esym (cast_obligation_1 Heq).1))).
      reflexivity.
Qed.

(* Qubit vector combination. An m-qubit vector and an n-qubit vector can be combined (by taking their tensor
 * product) into an m+n-qubit vector. *)
Program Definition combine (m n: nat) (q1: qubit_vector_of m) (q2: qubit_vector_of n): (qubit_vector_of (m+n)) :=
  (@QubitVectorMixin _ (castmx _ (vector q1 *t vector q2)) _).
Obligation 1.
  intros m n q1 q2; split; [ symmetry; apply expnD | auto ].
Qed.
Obligation 2.
  intros m n q1 q2. simpl.
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
    rewrite -Hq1. apply eq_bigr. intros i _. replace (q1 i 0) with (q1 i (Ordinal (mxtens_index_proof1 (m:=1) (n:=1) 0))).
      reflexivity. transitivity (q1 i (Ordinal (ltn0Sn 0))). replace (Ordinal (ltn0Sn 0)) with (Ordinal (mxtens_index_proof1 (m:=1) (n:=1) 0)).
      reflexivity. apply/val_eqP. simpl. auto.
      reflexivity.
    rewrite -Hq2. apply eq_bigr. intros i _. replace (q2 i 0) with (q2 i (Ordinal (mxtens_index_proof2 (m:=1) (n:=1) 0))).
      reflexivity. transitivity (q2 i (Ordinal (ltn0Sn 0))). replace (Ordinal (ltn0Sn 0)) with (Ordinal (mxtens_index_proof2 (m:=1) (n:=1) 0)).
      reflexivity. apply/val_eqP. simpl. auto.
      reflexivity.
    apply sum_cast with (combine_obligation_1 m n).1. auto. intros. rewrite castmxE. rewrite cast_ordK. rewrite cast_ord_id. reflexivity.
Qed.

(* Combine a list of k 1-qubit vectors into one k-qubit vector. We use the 0-qubit vector as an initial value
 * here, as it is the neutral element of the tensor product. *)
Program Fixpoint combine_list_aux (n: nat) (q: qubit_vector_of n) (k: nat) (l: list (qubit_vector_of 1)) (Hl: List.length l = k): (qubit_vector_of (n+k)) :=
  match l with
  | nil => q
  | h::t => (@combine_list_aux _ (combine q h) (k.-1) t _)
  end.
Obligation 1.
  intros. rewrite <- Hl. rewrite <- Heq_l. auto.
Qed.
Obligation 2.
  intros. rewrite <- Hl. rewrite <- Heq_l. auto.
Qed.
Obligation 3.
  intros. rewrite <- Hl. rewrite <- Heq_l. simpl. rewrite addn1. rewrite addSn. rewrite addnS //.
Qed.

Definition combine_list (k: nat) (l: list (qubit_vector_of 1)) (Hl: List.length l = k): (qubit_vector_of k) :=
  (combine_list_aux zero_qubit Hl).

(* Definition of decomposability. A qubit vector is decomposable if it can be written as the combination of
 * two qubit vectors. It is maximally decomposable if it can be written as a combination of 1-qubit vectors. *)
Definition decomposable_aux (p: nat) (q: qubit_vector_of p) (n m: nat) (Heq: (n + m = p)%N) :=
  exists (q1: qubit_vector_of n) (q2: qubit_vector_of m),
  (cast (combine q1 q2) Heq) = q.

Definition decomposable (p: nat) (q: qubit_vector_of p) :=
  exists n m Heq, (@decomposable_aux p q n m Heq).

Definition maximally_decomposable (n: nat) (q: qubit_vector_of n) :=
  exists (l: list (qubit_vector_of 1) | length l = n), combine_list (proj2_sig l) = q.

(* Definition of entanglement. A qubit vector is entangled if there are two qubits b1 and b2 such that measuring
 * b1 influences the probability distribution of measuring b2. It is maximally entangled if all qubits in the
 * vector influence each other. It is disentangled if no qubits in the vector influence each other. *)
Definition disentangled_aux (n: nat) (b1 b2: 'I_n) (q: qubit_vector_of n) :=
  prob_0 b1 (QubitVectorMixin (measure0_unitary b2 q)) = prob_0 b1 (QubitVectorMixin (measure1_unitary b2 q)) /\
  prob_1 b1 (QubitVectorMixin (measure0_unitary b2 q)) = prob_1 b1 (QubitVectorMixin (measure1_unitary b2 q)).

Definition disentangled (n: nat) (q: qubit_vector_of n) :=
  forall b1 b2, disentangled_aux b1 b2 q.

Definition maximally_entangled (n: nat) (q: qubit_vector_of n):
  forall b1 b2, ~disentangled_aux b1 b2 q.

(* Entanglement and decomposability are equivalent. *)
Theorem decdis n (q: qubit_vector_of n):
  maximally_decomposable q -> disentangled q.
Proof.
  unfold disentangled; unfold maximally_decomposable; unfold disentangled_aux; unfold measure_0; unfold measure_1;
  unfold prob_0; unfold prob_1; simpl.
    intros. destruct H. rewrite <- H. clear H. destruct x. unfold combine_list. simpl. split.
      apply congr_big; try auto.
      intros.

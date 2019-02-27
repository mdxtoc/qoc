Set Implicit Arguments.

From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Local Open Scope ring_scope.
Import Num.Theory GRing.Theory.

Require Import quantum IMonad.
From Coq.Logic Require Import JMeq FunctionalExtensionality.

(* The Qbit type is represented here by a (qubit_vector_of 1) *)

(* error state *)
Inductive QIO (A: Type): nat -> nat -> Type :=
  QReturn: forall {i}, A -> QIO A i i
| MkQbit: forall {i o}, (qubit_vector_of 1) -> (qubit_vector_of (S i) -> QIO A (S i) o) -> QIO A i o
| ApplyU: forall {i o}, gate_of i -> QIO A i o -> QIO A i o
| Meas: forall {i o}, qubit_vector_of i -> (bool -> QIO A i o) -> QIO A i o
| Error: forall {i o}, QIO A i o.

Program Fixpoint qio_bind {i o' o: nat} {A B}
  (z: QIO A i o') (f: A -> QIO B o' o): QIO B i o :=
  match z with
  | QReturn _ a => f a
  | MkQbit _ _ q g => MkQbit q (fun x => qio_bind (g x) f)
  | ApplyU _ _ u q => ApplyU u (qio_bind q f)
  | Meas _ _ x g => Meas x (fun b => qio_bind (g b) f)
  | Error _ _ => Error B
  end.
Solve All Obligations with intros; symmetry; assumption.

Program Instance qio_monad:
  IMonad (fun (i: nat) (o: nat) A => QIO A i o) :=
{
  unit i A x := QReturn x;
  IMonad.bind i o' o A B z f := qio_bind z f
}.
Obligation 1.
  reflexivity.
Qed.
Obligation 2.
  intros; simpl; induction x; simpl; try f_equal; try apply functional_extensionality;
    assumption.
Qed.
Obligation 3.
  intros; simpl; induction x; simpl; try f_equal; try apply functional_extensionality;
    [ intros; apply H | apply IHx | intros; apply H ].
Qed.

Fixpoint evalQIO {n m: nat} (A: Type) (z: QIO A n m)
  (v: qubit_vector_of n): A :=

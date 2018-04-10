Set Implicit Arguments.
Unset Strict Implicit.

Class GMonad (m : Type -> Type -> Type -> Type) :=
{
  gunit : forall {i a} (x : a), m i i a ;
  gbind : forall {i o' o a b}, m o' o a -> (a -> m i o' b) -> m i o b ;
  gbind_gunit_left : forall i o a b (x : a) (f : a -> m i o b), gbind (gunit x) f = f x ;
  gbind_gunit_right : forall i o a (x : m i o a), gbind x gunit = x ;
  gbind_assoc : forall i o' o'' o a b c (x : m o'' o a) (f : a -> m o' o'' b) (g : b -> m i o' c),
    gbind x (fun a : a => gbind (f a) g) = gbind (gbind x f) g
}.

Notation "T >>== U" := (gbind T U) (at level 20).
Notation "x <-- T ;; E" := (gbind T (fun x : _ => E)) (at level 30, right associativity).
Notation "'ret' t" := (gunit t) (at level 20).

Definition gjoin {I O O' A B m} `{ GMonad m } (e1 : m O' O (A -> m I O' B)) (x : A) : m I O B :=
  f <-- e1 ;; f x.

Class Monad (m: Type -> Type): Type :=
{ return_: forall {A}, A -> m A;
  bind_: forall {A}, m A -> forall {B}, (A -> m B) -> m B;
  right_unit: forall A (a: m A), a = bind_ a (@return_ A);
  left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind_ (return_ a) f;
  associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind_ ma (fun x => bind_ (f x) g) = bind_ (bind_ ma f) g
}.

Require Import Coq.Program.Tactics.
Instance monad_is_gmonad {m} `{Monad m}: GMonad (fun i o => m) :=
{
  gunit i a x := return_ x;
  gbind i o o' a b m f := bind_ m f
}.
Proof.
  symmetry; apply left_unit.
  symmetry; apply right_unit.
  intros; apply associativity.
Qed.

From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Local Open Scope ring_scope.
Import Num.Theory GRing.Theory.

Require Import quantum.

(* The Qbit type is represented here by a (qubit_vector_of 1) *)

Definition Qbit := qubit_vector_of 1.
Definition U := gate_of 1.
Inductive QIO (a: Type): Type :=
  QReturn: a -> QIO a
| MkQbit: bool -> (Qbit -> QIO a) -> QIO a
| ApplyU: U -> QIO a -> QIO a
| Meas: Qbit -> (bool -> QIO a) -> QIO a.

Fixpoint qio_bind {A: Type} (z: QIO A) {B: Type} (f: A -> QIO B) :=
  match z with
  | QReturn a => f a
  | MkQbit b g => MkQbit b (fun x => qio_bind (g x) f)
  | ApplyU u q => ApplyU u (qio_bind q f)
  | Meas x g => Meas x (fun b => qio_bind (g b) f)
  end.

Require Import Coq.Logic.FunctionalExtensionality.
Instance qio_monad: Monad QIO := 
{
  return_ := QReturn;
  bind_ _ z _ f := qio_bind z f
}.
Proof.
  intros. induction a; simpl;
  [ 
  | f_equal; extensionality x; rewrite {1}H
  | rewrite {1}IHa
  | f_equal; extensionality x; rewrite {1}H
  ];
  try reflexivity.
  intros; simpl; reflexivity.
  intros; induction ma; simpl;
  [ reflexivity 
  | f_equal; extensionality x; apply H
  | f_equal; apply IHma
  | f_equal; extensionality x; apply H
  ].
Qed.

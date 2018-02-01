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
{ return_: forall A, A -> m A;
  bind: forall A, m A -> forall B, (A -> m B) -> m B;
  right_unit: forall A (a: m A), a = bind a (@return_ A);
  left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind (return_ a) f;
  associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun x => bind (f x) g) = bind (bind ma f) g
}.

Require Import Coq.Program.Tactics.
Program Instance monad_is_gmonad {m} `{Monad m}: GMonad (fun i o => m) :=
{
  gunit i a x := return_ x;
  gbind i o o' a b m f := bind m f
}.
Obligation 1.
  symmetry; apply left_unit.
Qed.
Obligation 2.
  symmetry; apply right_unit.
Qed.
Obligation 3.
  apply associativity.
Qed.

From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed.
Local Open Scope ring_scope.
Import Num.Theory GRing.Theory.

Require Import quantum.
Program Instance blerp: Monad (list (R[i] * qubit_mixin_of n)).
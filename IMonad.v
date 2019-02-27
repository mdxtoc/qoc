Set Implicit Arguments.
Unset Strict Implicit.

Class IMonad (I: Set) (m : I -> I -> Type -> Type) :=
{
  unit: forall {i: I} {A} (x: A), m i i A;
  bind: forall {i o' o A B}, m i o' A -> (A -> m o' o B) -> m i o B;
  bind_unit_left: forall i o A B (x: A) (f : A -> m i o B),
    bind (unit x) f = f x;
  bind_unit_right: forall i o A (x: m i o A),
    bind x unit = x;
  bind_assoc: forall i o' o'' o A B C (x: m i o' A) (f: A -> m o' o'' B) (g: B -> m o'' o C),
    bind x (fun a: A => bind (f a) g) = bind (bind x f) g
}.

Notation "T >>== U" := (bind T U) (at level 20).
Notation "x <-- T ;; E" := (bind T (fun x : _ => E)) (at level 30, right associativity).
Notation "'ret' t" := (unit t) (at level 20).

Definition gjoin {I i o' o} {A B m} `{ IMonad I m }
  (e1 : m i o' (A -> m o' o B)) (x : A) : m i o B :=
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


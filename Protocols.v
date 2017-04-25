From mathcomp Require Import all_ssreflect all_algebra all_field all_real_closed. 
(*
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory. 
Require Import List.
*)
Require Import complex_stuff.
Require Import quantum.

Inductive Gate : Type := 
   | H: Gate
   | alpha: nat -> Gate
   | gate: forall n: nat, gate_mixin_of n -> Gate.

Inductive Expr: Type := 
   | var : nat -> Expr
   | plus: Expr -> Expr -> Expr
   | measure: list nat -> Expr -> Expr 
   | apply : list nat -> Expr -> Expr
   | op : Gate -> Expr
   | chan: nat -> Expr.


Inductive Proc: Type := 
   | Null : Proc
   | Par: Proc -> Proc -> Proc
   | Rec: Expr -> Expr -> Proc -> Proc
   | Send: Expr -> Expr -> Proc -> Proc
   | Act: Expr -> Proc -> Proc.

(* Internal Syntax = Evaluation Contexts *)
Inductive Econtext : Set :=
   | echole : Econtext
   | ecmeasure : list nat -> Econtext -> Econtext
   | ecapply: list nat -> Econtext -> Econtext.

Inductive Fcontext : Type :=
   | fcRecChan : Econtext -> Expr -> Proc -> Fcontext
   | fcSendChan : Expr -> Econtext -> Proc -> Fcontext
   | fcAct: Econtext -> Proc -> Fcontext.

Function eFill (e: Econtext)(x: Expr): Expr :=
    match e with
     | echole => x
     | ecmeasure l E => measure l (eFill E x)
     | ecapply l E => apply l (eFill E x)
    end.

Function Fill (f: Fcontext)(x: Expr): Proc :=
match f with 
     | fcRecChan E n p => Rec (eFill E x) n p
     | fcSendChan e E p => Send e (eFill E x) p
     | fcAct E p => Act (eFill E x) p
end.

(* The following is experimental, i.e. doesn't compile since
   the interface to quantum.v is yet in the dark..
-->  I assume a function (probably based on measure_1) 
  >> measure (n: nat)(q: qubit): list(real * qubit)
    measuring the nth bit in a qubit and returning the probs for 0 and 1
    together with the respective successor qubit vector as the first two 
    pais in the result list *)
Parameter measure_p: forall (n: nat)  (i: 'I_n) (q: qubit_mixin_of n),
           list ((R [i])* qubit_mixin_of n).

Print measure_p.
Check 3 * 5.
Lemma blu: forall (x: R [i]), x + x = x.

Function bla (x: R[i]) := (x * x)%C.

Function measure_rep n (i: 'I_n) (ql : list ((R [i]) * qubit_mixin_of n)): 
             (list ((R [i]) * qubit_mixin_of n)) :=
match ql with
  | List.nil => List.nil
  | (q :: ql')%list =>
      let pqpq := measure_p n i (snd q) in
      let pq := (fst q) in
      match pqpq with 
         | List.nil => List.nil 
         | ((p0%C,q0) :: l1)%list =>
          match  l1 with
          | List.nil => List.nil
          | ((p1%C,q1) :: l2)%list =>   
              let pn0 := (p0 * pq) in
              let pn1 := p1 in
                 (((pn0)%C,q0):: (((pn1,q1) :: (measure_rep n i ql'))))
          end
      end
end.


 





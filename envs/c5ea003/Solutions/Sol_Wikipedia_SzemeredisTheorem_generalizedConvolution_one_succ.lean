-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.generalizedConvolution_one_succ
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:11:52.621605+00:00
-- url     : https://prove2.me/submissions/b2f9a989-4d6c-4ff0-b12c-ee5d83ed1f7d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































end Wikipedia.SzemeredisTheorem

end

section


/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





















@[simp]
theorem fiberConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (z : G) :
    fiberConvolution 0 w z =
      zeroFiberDelta z * w (fun i => Fin.elim0 i) :=
  rfl





@[simp]
theorem cutTestProduct_one {G : Type*} {r : ℕ} (x : Fin r → G) :
    cutTestProduct
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) x = 1 := by
  simp [cutTestProduct]













@[simp]
theorem generalizedConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1)) (z : G) :
    generalizedConvolution (n + 1) u z =
      mean fun y : Fin n → G =>
        cutTestProduct u (sumFiberTuple n z y) :=
  rfl











































end Wikipedia.SzemeredisTheorem

end
/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
@[simp]
theorem solution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ)) z = 1 := by
  rw [generalizedConvolution_succ]
  calc
    mean (fun y : Fin n → G =>
        cutTestProduct
          (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ))
          (sumFiberTuple n z y)) =
        mean (fun _ : Fin n → G => (1 : ℝ)) := by
      apply congrArg mean
      funext y
      exact cutTestProduct_one (sumFiberTuple n z y)
    _ = 1 := mean_const 1

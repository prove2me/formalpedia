-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.dual_apply_dualErrorVector
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:09:38.371981+00:00
-- url     : https://prove2.me/submissions/2b1dc525-b060-4cb1-bc6b-cf005e7b675e

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_dual_apply_eq_sum_coefficient

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/
open Wikipedia.SzemeredisTheorem
open scoped Pointwise

open Wikipedia.SzemeredisTheorem in
/-- Exact support value of the error cube under a dual functional. -/
theorem solution
    {τ : Type*} [Fintype τ]
    (ε : ℝ) (L : StrongDual ℝ (τ → ℝ)) :
    L (dualErrorVector ε L) =
      ε * coefficientL1 (dualCoefficient L) := by
  rw [dual_apply_eq_sum_coefficient]
  calc
    (∑ t, dualCoefficient L t * dualErrorVector ε L t) =
        ∑ t, ε * |dualCoefficient L t| := by
      apply Fintype.sum_congr
      intro t
      rw [dualErrorVector]
      rw [← self_mul_sign (dualCoefficient L t)]
      ring
    _ = ε * coefficientL1 (dualCoefficient L) := by
      rw [coefficientL1, Finset.mul_sum]

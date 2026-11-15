-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.dual_apply_eq_sum_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:02:32.55866+00:00
-- url     : https://prove2.me/submissions/ce562d23-d07d-47aa-8e5b-e0401804d41e

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

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
/-- Every continuous linear functional on a finite function space is the
dot product with its coordinate vector. -/
theorem solution
    {τ : Type*} [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ)) (v : τ → ℝ) :
    L v = ∑ t, dualCoefficient L t * v t := by
  classical
  calc
    L v =
        L (∑ t, (v t) •
          Pi.single (M := fun _ : τ => ℝ) t 1) := by
      rw [← pi_eq_sum_univ' v]
    _ = ∑ t,
        L ((v t) •
          Pi.single (M := fun _ : τ => ℝ) t 1) := by
      exact map_sum L _ _
    _ = ∑ t, dualCoefficient L t * v t := by
      apply Fintype.sum_congr
      intro t
      rw [map_smul]
      simp [dualCoefficient, mul_comm]

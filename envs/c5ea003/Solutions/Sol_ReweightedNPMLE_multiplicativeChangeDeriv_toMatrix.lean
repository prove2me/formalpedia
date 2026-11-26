-- Prove2me | solution 1 for ReweightedNPMLE.multiplicativeChangeDeriv_toMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:02:23.062803+00:00
-- url     : https://prove2.me/submissions/a0f83acc-7de6-4fb1-9c30-f6d2d4843133

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Injective change of variables for determinant moments

This file packages the precise area-formula step used by the paper's
determinant-moment argument.  If an injective differentiable map sends a
localized event into a probability density, its density-weighted Jacobian
has integral at most one.  A pointwise Jacobian/density comparison then
transfers that bound to the desired random variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Standard-basis matrix of the derivative of the multiplicative change
map.  This is `diag(1+t) + diag(w) Dt`. -/
theorem solution
    {n : ℕ} (w u : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    LinearMap.toMatrix' (w • L + (1 + u) •
      ContinuousLinearMap.id ℝ (Fin n → ℝ)).toLinearMap =
      Matrix.diagonal (fun i ↦ 1 + u i) +
        Matrix.diagonal w * LinearMap.toMatrix' L.toLinearMap := by
  classical
  ext i j
  have hmul : (Matrix.diagonal w * LinearMap.toMatrix' L.toLinearMap) i j =
      w i * L (Pi.single j 1) i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [LinearMap.toMatrix'_apply]
    · intro b hb hbi
      simp [Ne.symm hbi]
    · simp
  rw [Matrix.add_apply, hmul]
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrix'_apply]
    ring
  · simp [LinearMap.toMatrix'_apply, hij]

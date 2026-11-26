-- Prove2me | solution 1 for ReweightedNPMLE.gaussianMomentHellingerError_le_stirling
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:07:43.524556+00:00
-- url     : https://prove2.me/submissions/b92c5a2a-5cf3-43c5-b836-21993be2ec61

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_pow_div_factorial_le_stirling

/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The global moment-matching error with its factorial eliminated by the
effective Stirling bound. -/
theorem solution {S : ℝ} (hS : 0 ≤ S)
    (L : ℕ) :
    gaussianMomentHellingerError S L ≤
      (4 * Real.exp (S ^ 2) *
        (Real.exp 1 * S ^ 2 / (2 * L + 1)) ^ (2 * L + 1)) ^
          (1 / 2 : ℝ) := by
  unfold gaussianMomentHellingerError
  have hratio :
      (S ^ 2) ^ (2 * L + 1) / ((2 * L + 1).factorial : ℝ) ≤
        (Real.exp 1 * S ^ 2 / (2 * L + 1)) ^ (2 * L + 1) := by
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_ofNat] using
      (pow_div_factorial_le_stirling (sq_nonneg S)
        (Nat.zero_lt_succ (2 * L)))
  have hinside :
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (2 * L + 1) /
          ((2 * L + 1).factorial : ℝ)) ≤
        4 * Real.exp (S ^ 2) *
          (Real.exp 1 * S ^ 2 / (2 * L + 1)) ^ (2 * L + 1) := by
    calc
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (2 * L + 1) /
          ((2 * L + 1).factorial : ℝ)) =
          (4 * Real.exp (S ^ 2)) *
            ((S ^ 2) ^ (2 * L + 1) /
              ((2 * L + 1).factorial : ℝ)) := by ring
      _ ≤ (4 * Real.exp (S ^ 2)) *
          (Real.exp 1 * S ^ 2 / (2 * L + 1)) ^ (2 * L + 1) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact hinside

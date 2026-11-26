-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianMomentHellingerError_256_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:09:30.331802+00:00
-- url     : https://prove2.me/submissions/3aae4bb7-c3db-464e-ae11-ca7163144cea

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
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianMomentHellingerError_paper_le

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
/-- At the fixed order constant used below, the global Hellinger remainder
is eventually smaller than `1/n`. -/
theorem solution
    {S : ℝ} (hS : 0 ≤ S) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentHellingerError S (gaussianPaperMomentOrder 256 n) ≤
        1 / (n : ℝ) := by
  let A := 4 * Real.exp (S ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventually_gaussianMomentHellingerError_paper_le
      (show (0 : ℝ) < 256 by norm_num) hS,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop A,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hglobal hAn hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hA30 : A ≤ (n : ℝ) ^ 30 := by
    calc
      A ≤ (n : ℝ) := hAn
      _ = (n : ℝ) ^ 1 := by ring
      _ ≤ (n : ℝ) ^ 30 := pow_le_pow_right₀ hnOne (by omega)
  have hinside : A * (n : ℝ) ^ (-256 / 8 : ℝ) ≤
      1 / (n : ℝ) ^ 2 := by
    have hneg : (n : ℝ) ^ (-256 / 8 : ℝ) = 1 / (n : ℝ) ^ 32 := by
      norm_num [Real.rpow_neg_natCast, zpow_neg, div_eq_mul_inv]
      rfl
    rw [hneg]
    calc
      A * (1 / (n : ℝ) ^ 32) ≤
          (n : ℝ) ^ 30 * (1 / (n : ℝ) ^ 32) := by gcongr
      _ = 1 / (n : ℝ) ^ 2 := by field_simp
  calc
    gaussianMomentHellingerError S (gaussianPaperMomentOrder 256 n) ≤
        (A * (n : ℝ) ^ (-256 / 8 : ℝ)) ^ (1 / 2 : ℝ) := by
      simpa only [A] using hglobal
    _ ≤ (1 / (n : ℝ) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hinside (by norm_num)
    _ = 1 / (n : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      have hsquare : 1 / (n : ℝ) ^ 2 = (1 / (n : ℝ)) ^ 2 := by
        field_simp
      rw [hsquare, Real.sqrt_sq (by positivity)]

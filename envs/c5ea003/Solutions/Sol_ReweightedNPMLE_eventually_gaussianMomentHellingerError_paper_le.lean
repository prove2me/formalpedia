-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianMomentHellingerError_paper_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:31.125045+00:00
-- url     : https://prove2.me/submissions/7ff8f3e7-cdcb-48b4-9215-0e172d7ae919

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
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperStirlingBase_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperStirlingPower_le
import Theorems.Thm_ReweightedNPMLE_gaussianMomentHellingerError_le_stirling

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
/-- The global moment-matching Hellinger error inherits the same inverse
power before taking its square root. -/
theorem solution
    {C S : ℝ} (hC : 0 < C) (hS : 0 ≤ S) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentHellingerError S (gaussianPaperMomentOrder C n) ≤
        (4 * Real.exp (S ^ 2) * (n : ℝ) ^ (-C / 8 : ℝ)) ^
          (1 / 2 : ℝ) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gaussianPaperStirlingBase_le 0 hC hS
      (show (0 : ℝ) ≤ 0 by norm_num),
    eventually_gaussianPaperStirlingPower_le hC,
    hlog.eventually_ge_atTop 1] with n hbase hpower hlogn
  let L := gaussianPaperMomentOrder C n
  let A := gaussianPaperTaylorArgument 0 S 0 n
  let ρ := Real.log (n : ℝ) ^ (-1 / 8 : ℝ)
  have hA : S ^ 2 ≤ A := by
    dsimp [A, gaussianPaperTaylorArgument, gaussianPaperSampleRadius,
      gaussianPaperRadiusExponent]
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, add_zero]
    nlinarith [sq_nonneg S]
  have hcompare :
      Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ) ≤
        Real.exp 1 * A / ((L : ℝ) + 1) := by
    calc
      Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ) ≤
          Real.exp 1 * S ^ 2 / ((L : ℝ) + 1) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact_mod_cast (show L + 1 ≤ 2 * L + 1 by omega)
      _ ≤ Real.exp 1 * A / ((L : ℝ) + 1) := by
        gcongr
  have hbase' :
      Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ) ≤ ρ :=
    hcompare.trans (by simpa only [A, L, ρ] using hbase)
  have hbase0 : 0 ≤
      Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ) := by positivity
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    dsimp [ρ]
    exact Real.rpow_le_one_of_one_le_of_nonpos hlogn (by norm_num)
  have hbasePow :
      (Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ)) ^ (2 * L + 1) ≤
        ρ ^ (2 * L + 1) := pow_le_pow_left₀ hbase0 hbase' _
  have hdegree : ρ ^ (2 * L + 1) ≤ ρ ^ (L + 1) := by
    exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
  have hρpower : ρ ^ (L + 1) ≤ (n : ℝ) ^ (-C / 8 : ℝ) := by
    simpa only [ρ, L] using hpower
  have hstirling := gaussianMomentHellingerError_le_stirling hS L
  calc
    gaussianMomentHellingerError S L ≤
        (4 * Real.exp (S ^ 2) *
          (Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ)) ^
            (2 * L + 1)) ^ (1 / 2 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
        hstirling
    _ ≤ (4 * Real.exp (S ^ 2) * (n : ℝ) ^ (-C / 8 : ℝ)) ^
        (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      gcongr
      exact hbasePow.trans (hdegree.trans hρpower)

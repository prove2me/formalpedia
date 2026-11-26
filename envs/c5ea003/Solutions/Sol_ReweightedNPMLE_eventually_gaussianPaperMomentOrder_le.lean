-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianPaperMomentOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:07:45.281827+00:00
-- url     : https://prove2.me/submissions/f3c5081a-c323-4a23-88e7-086ee2a542ce

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
import Theorems.Thm_ReweightedNPMLE_tendsto_id_div_log_atTop

-- Inline helpers preserved from ReweightedNPMLE.GaussianNearMLERate.
section
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

namespace ReweightedNPMLE











/-- The logarithmic Taylor scale diverges. -/
theorem tendsto_gaussianPaperLogScale_atTop :
    Filter.Tendsto gaussianPaperLogScale Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [gaussianPaperLogScale] using tendsto_id_div_log_atTop.comp hlog



/-- Taking the natural ceiling does not alter the asymptotic Taylor scale. -/
theorem tendsto_gaussianPaperMomentOrder_div {C : ℝ} (hC : 0 < C) :
    Filter.Tendsto
      (fun n ↦ (gaussianPaperMomentOrder C n : ℝ) /
        (C * gaussianPaperLogScale n))
      Filter.atTop (𝓝 1) := by
  have hbase : Filter.Tendsto (fun n ↦ C * gaussianPaperLogScale n)
      Filter.atTop Filter.atTop :=
    tendsto_gaussianPaperLogScale_atTop.const_mul_atTop hC
  simpa only [gaussianPaperMomentOrder] using
    (tendsto_nat_ceil_div_atTop (R := ℝ)).comp hbase





























































































end ReweightedNPMLE
end

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
/-- Eventually the ceiling order is at most twice its unrounded value. -/
theorem solution {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in Filter.atTop,
      (gaussianPaperMomentOrder C n : ℝ) ≤
        2 * C * gaussianPaperLogScale n := by
  have hratio := tendsto_gaussianPaperMomentOrder_div hC
  have hlt : ∀ᶠ n in Filter.atTop,
      (gaussianPaperMomentOrder C n : ℝ) /
          (C * gaussianPaperLogScale n) < 2 :=
    hratio.eventually_lt_const (by norm_num)
  have hpos : ∀ᶠ n in Filter.atTop,
      0 < C * gaussianPaperLogScale n :=
    (tendsto_gaussianPaperLogScale_atTop.const_mul_atTop hC).eventually_gt_atTop 0
  filter_upwards [hlt, hpos] with n hn hden
  have := (div_lt_iff₀ hden).mp hn
  nlinarith

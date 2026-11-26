-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianPaperStirlingPower_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:06:19.58321+00:00
-- url     : https://prove2.me/submissions/4ddf43d8-491d-4297-a6b5-d22dc2a549f5

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
/-- Raising the logarithmic Stirling base to the paper order converts it
into a genuine inverse power of the sample size. -/
theorem solution
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Real.log (n : ℝ) ^ (-1 / 8 : ℝ)) ^
          (gaussianPaperMomentOrder C n + 1) ≤
        (n : ℝ) ^ (-C / 8 : ℝ) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually_gt_atTop 1,
    hloglog.eventually_gt_atTop 0, Filter.eventually_ge_atTop (2 : ℕ)]
      with n hlogn hloglogn hn
  let x := Real.log (n : ℝ)
  let y := Real.log x
  let L := gaussianPaperMomentOrder C n
  have hx : 0 < x := lt_trans zero_lt_one hlogn
  have hy : 0 < y := by simpa only [x, y] using hloglogn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hceil : C * (x / y) ≤ (L : ℝ) := by
    simpa only [L, gaussianPaperMomentOrder, gaussianPaperLogScale, x, y] using
      (Nat.le_ceil (C * gaussianPaperLogScale n))
  have horder : C * x ≤ y * ((L : ℝ) + 1) := by
    have hceil' : C * x / y ≤ (L : ℝ) := by
      convert hceil using 1 <;> ring
    have := (div_le_iff₀ hy).mp hceil'
    nlinarith
  calc
    (x ^ (-1 / 8 : ℝ)) ^ (L + 1) =
        (x ^ (-1 / 8 : ℝ)) ^ (((L + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    _ = x ^ ((-1 / 8 : ℝ) * ((L : ℝ) + 1)) := by
      rw [Real.rpow_mul hx.le]
      norm_num
    _ = Real.exp (Real.log x *
        ((-1 / 8 : ℝ) * ((L : ℝ) + 1))) :=
      Real.rpow_def_of_pos hx _
    _ ≤ Real.exp (Real.log (n : ℝ) * (-C / 8 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      change y * ((-1 / 8 : ℝ) * ((L : ℝ) + 1)) ≤
        x * (-C / 8 : ℝ)
      nlinarith
    _ = (n : ℝ) ^ (-C / 8 : ℝ) :=
      (Real.rpow_def_of_pos hnreal _).symm

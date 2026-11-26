-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianPaperSampleRadius_add_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:07:06.619554+00:00
-- url     : https://prove2.me/submissions/5695d763-76d3-4257-b129-0b0c51e04254

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
/-- The paper sample radius is negligible compared with even `n²`; this
coarse form is sufficient for the mesh contribution to the log error. -/
theorem solution
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianPaperSampleRadius d S b n + S ≤ (n : ℝ) ^ 2 := by
  let D : ℝ := 2 * S + Real.sqrt (d : ℝ) * Real.sqrt (2 * (b + 4))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop D,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hlogn hDn hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogle : Real.log (n : ℝ) ≤ (n : ℝ) :=
    (Real.log_le_sub_one_of_pos hnreal).trans (by linarith)
  have hsqrtlog : Real.sqrt (Real.log (n : ℝ)) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hsqrtOne : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlogn
  have hb4 : 0 ≤ 2 * (b + 4) := by positivity
  unfold gaussianPaperSampleRadius gaussianPaperRadiusExponent
  rw [show 2 * ((b + 4) * Real.log (n : ℝ)) =
      (2 * (b + 4)) * Real.log (n : ℝ) by ring,
    Real.sqrt_mul hb4]
  have hsqrtd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsqrtb : 0 ≤ Real.sqrt (2 * (b + 4)) := Real.sqrt_nonneg _
  calc
    S + Real.sqrt (d : ℝ) *
          (Real.sqrt (2 * (b + 4)) * Real.sqrt (Real.log (n : ℝ))) + S =
        2 * S + (Real.sqrt (d : ℝ) * Real.sqrt (2 * (b + 4))) *
          Real.sqrt (Real.log (n : ℝ)) := by ring
    _ ≤ D * Real.sqrt (Real.log (n : ℝ)) := by
      dsimp [D]
      nlinarith
    _ ≤ (n : ℝ) * (n : ℝ) := by gcongr
    _ = (n : ℝ) ^ 2 := by ring

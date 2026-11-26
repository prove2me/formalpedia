-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianMomentDimension_le_logScale_pow
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:32.650504+00:00
-- url     : https://prove2.me/submissions/df3d47b8-c836-4adf-b49c-3c6d3c4f8a62

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
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperMomentOrder_le
import Theorems.Thm_ReweightedNPMLE_tendsto_id_div_log_atTop

-- Inline helpers preserved from ReweightedNPMLE.PolynomialMoments.
section
namespace ReweightedNPMLE

open scoped BigOperators
open Finset Fintype



/-- There are exactly `choose (D + d) d` monomials of total degree at most `D`. -/
theorem card_monomialCoord (d D : ℕ) :
    Fintype.card (MonomialCoord d D) = (D + d).choose d := by
  rw [Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : d + 1 + D - 1 = D + d := by omega
  rw [h, Nat.choose_symm_add]











/-- The ambient dimension of the moment feature is the number of monomials. -/
theorem finrank_monomialFeature (d D : ℕ) :
    Module.finrank ℝ (MonomialCoord d D → ℝ) = (D + d).choose d := by
  rw [Module.finrank_fintype_fun_eq_card, card_monomialCoord]













































































































end ReweightedNPMLE
end

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
/-- The moment dimension has precisely the polylogarithmic order required by
the paper, in an explicit eventual inequality. -/
theorem solution
    (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in Filter.atTop,
      (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) ≤
        ((4 * C + 1) * gaussianPaperLogScale n) ^ d := by
  filter_upwards [eventually_gaussianPaperMomentOrder_le hC,
    tendsto_gaussianPaperLogScale_atTop.eventually_gt_atTop (d : ℝ)]
      with n hm hs
  let L := gaussianPaperMomentOrder C n
  have hkNat : gaussianMomentDimension d L ≤ (2 * L + d) ^ d := by
    change Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) ≤ _
    rw [finrank_monomialFeature]
    exact Nat.choose_le_pow _ _
  have hkReal : (gaussianMomentDimension d L : ℝ) ≤
      (((2 * L + d : ℕ) : ℝ) ^ d) := by exact_mod_cast hkNat
  have hscale : 0 ≤ gaussianPaperLogScale n := by
    exact (Nat.cast_nonneg d).trans hs.le
  have hbase : (2 * L + d : ℝ) ≤
      (4 * C + 1) * gaussianPaperLogScale n := by
    change 2 * (L : ℝ) + d ≤ _
    nlinarith
  calc
    (gaussianMomentDimension d L : ℝ) ≤
        (((2 * L + d : ℕ) : ℝ) ^ d) := hkReal
    _ = (2 * (L : ℝ) + d) ^ d := by push_cast; rfl
    _ ≤ ((4 * C + 1) * gaussianPaperLogScale n) ^ d :=
      pow_le_pow_left₀ (by positivity) hbase d

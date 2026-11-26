-- Prove2me | solution 1 for ReweightedNPMLE.general_finite_moment_matching_weightedL2_bound
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:09:18.324344+00:00
-- url     : https://prove2.me/submissions/5e559a5a-bc69-4f37-ba41-3d24807cd150

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Theorems.Thm_ReweightedNPMLE_abs_general_finite_remainder_quadratic_le
import Theorems.Thm_ReweightedNPMLE_general_finite_quadratic_eq_remainder_of_moment_match
import Theorems.Thm_ReweightedNPMLE_integral_gaussianMixture_sub_finite_sq_div_density

/-!
# Global Hellinger control from arbitrary mixing laws

The Gaussian overlap/Fubini identities in this file connect a general
probability mixing law to a finitely supported moment-matching law.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Global weighted `L²` moment-tail bound between an arbitrary probability
mixing law and a moment-matching finite probability law. -/
theorem solution
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    ∫ x : Point d,
        (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
          gaussianDensity d x ≤
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
        (L + 1).factorial) := by
  calc
    (∫ x : Point d,
        (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
          gaussianDensity d x) =
        (∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ) -
          2 * (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) +
          ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j)) :=
      integral_gaussianMixture_sub_finite_sq_div_density
        μ θ hθmeas w z hS hθS hzS
    _ = (∫ a, ∫ b,
          pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j *
          pointInnerExpRemainder L (z i) (z j) :=
      general_finite_quadratic_eq_remainder_of_moment_match
        μ θ hθmeas w z hint hmom hS hθS hzS
    _ ≤ |(∫ a, ∫ b,
          pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j *
          pointInnerExpRemainder L (z i) (z j)| := le_abs_self _
    _ ≤ 4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
        (L + 1).factorial) :=
      abs_general_finite_remainder_quadratic_le
        μ θ hθmeas w z hw hwsum hS hθS hzS

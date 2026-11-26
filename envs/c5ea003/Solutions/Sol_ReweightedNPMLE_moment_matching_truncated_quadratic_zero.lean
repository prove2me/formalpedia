-- Prove2me | solution 1 for ReweightedNPMLE.moment_matching_truncated_quadratic_zero
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:03:43.375163+00:00
-- url     : https://prove2.me/submissions/f58f7738-cf39-4d4c-9537-ba4db65d72c6

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
import Theorems.Thm_ReweightedNPMLE_IsMonomialCombination_integrable_comp_of_feature
import Theorems.Thm_ReweightedNPMLE_IsMonomialCombination_weighted_sum_eq_integral

-- Inline helpers preserved from ReweightedNPMLE.PolynomialMoments.
section
namespace ReweightedNPMLE

open scoped BigOperators
open Finset Fintype







































































/-- Native Euclidean inner products agree with the explicit coordinate dot
product. -/
theorem inner_eq_coordinateDot {d : ℕ} (x θ : Point d) :
    inner ℝ x θ = coordinateDot (fun i ↦ x i) (fun i ↦ θ i) := by
  rw [coordinateDot, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  apply Fintype.sum_congr
  intro i
  ring





















































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureMeasureHellinger.
section
/-!
# Global Hellinger control from arbitrary mixing laws

The Gaussian overlap/Fubini identities in this file connect a general
probability mixing law to a finitely supported moment-matching law.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE









theorem pointTruncatedInnerExp_comp_integrable
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (θ : Θ → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (y : Point d) :
    Integrable (fun a ↦ pointTruncatedInnerExp L (θ a) y) μ := by
  have h := (coordinateTruncatedInnerExp_isMonomialCombination
    L (fun r ↦ y r)).integrable_comp_of_feature
      μ (fun a r ↦ θ a r) hint
  apply h.congr
  exact Filter.Eventually.of_forall fun a ↦ by
    simp only [pointTruncatedInnerExp, coordinateTruncatedInnerExp,
      inner_eq_coordinateDot, real_inner_comm]

theorem moment_matching_pointTruncatedInnerExp_integral
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) (θ : Θ → Point d)
    (w : ι → ℝ) (z : ι → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    (y : Point d) :
    ∑ i, w i * pointTruncatedInnerExp L (z i) y =
      ∫ a, pointTruncatedInnerExp L (θ a) y ∂μ := by
  have h := (coordinateTruncatedInnerExp_isMonomialCombination
    L (fun r ↦ y r)).weighted_sum_eq_integral
      w (fun i r ↦ z i r) μ (fun a r ↦ θ a r) hint hmom
  simpa only [pointTruncatedInnerExp, coordinateTruncatedInnerExp,
    inner_eq_coordinateDot, real_inner_comm] using h

theorem pointTruncatedInnerExp_comm {d : ℕ} (L : ℕ) (x y : Point d) :
    pointTruncatedInnerExp L x y = pointTruncatedInnerExp L y x := by
  unfold pointTruncatedInnerExp
  rw [real_inner_comm]

























end ReweightedNPMLE
end

/-!
# Global Hellinger control from arbitrary mixing laws

The Gaussian overlap/Fubini identities in this file connect a general
probability mixing law to a finitely supported moment-matching law.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Exact moment matching annihilates the entire truncated part of the
general-law/finite-law Gaussian overlap quadratic form. -/
theorem solution
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) (θ : Θ → Point d)
    (w : ι → ℝ) (z : ι → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ) :
    (∫ a, ∫ b, pointTruncatedInnerExp L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointTruncatedInnerExp L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j * pointTruncatedInnerExp L (z i) (z j) = 0 := by
  have hcomponent (i : ι) : Integrable (fun a ↦
      w i * pointTruncatedInnerExp L (θ a) (z i)) μ :=
    (pointTruncatedInnerExp_comp_integrable μ θ hint (z i)).const_mul (w i)
  have hA :
      (∫ a, ∫ b, pointTruncatedInnerExp L (θ b) (θ a) ∂μ ∂μ) =
        ∑ i, w i * ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
    calc
      (∫ a, ∫ b, pointTruncatedInnerExp L (θ b) (θ a) ∂μ ∂μ) =
          ∫ a, ∑ i, w i * pointTruncatedInnerExp L (z i) (θ a) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a ↦
          (moment_matching_pointTruncatedInnerExp_integral
            μ θ w z hint hmom (θ a)).symm
      _ = ∫ a, ∑ i, w i * pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a ↦ by
          apply Finset.sum_congr rfl
          intro i _
          rw [pointTruncatedInnerExp_comm]
      _ = ∑ i, ∫ a, w i * pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
        exact integral_finsetSum Finset.univ fun i _ ↦ hcomponent i
      _ = ∑ i, w i * ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
  have hB :
      (∑ i, w i * ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ) =
        ∑ i, ∑ j, w i * w j * pointTruncatedInnerExp L (z i) (z j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← moment_matching_pointTruncatedInnerExp_integral μ θ w z hint hmom (z i)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pointTruncatedInnerExp_comm L (z j) (z i)]
    ring
  rw [hA, hB]
  ring

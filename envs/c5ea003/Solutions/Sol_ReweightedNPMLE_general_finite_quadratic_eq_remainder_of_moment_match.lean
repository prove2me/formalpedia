-- Prove2me | solution 1 for ReweightedNPMLE.general_finite_quadratic_eq_remainder_of_moment_match
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:26.461085+00:00
-- url     : https://prove2.me/submissions/7e4de4df-bf25-4dc2-ae2e-d1c25911367a

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
import Theorems.Thm_ReweightedNPMLE_exp_inner_comp_comp_integrable
import Theorems.Thm_ReweightedNPMLE_exp_inner_comp_integrable
import Theorems.Thm_ReweightedNPMLE_moment_matching_truncated_quadratic_zero
import Theorems.Thm_ReweightedNPMLE_real_exp_taylor_remainder_bound

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

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureHellinger.
section
/-!
# Global Hellinger control for finite Gaussian mixtures

This file combines the exact Gaussian overlap calculation with weighted
Cauchy--Schwarz.  It packages the difference of two finite mixtures as one
signed mixture and identifies its weighted `L²` error with a finite
exponential-kernel quadratic form.
-/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace ReweightedNPMLE















/-- Uniform Taylor bound for the inner-product exponential remainder on a
Euclidean ball. -/
theorem abs_pointInnerExpRemainder_le
    {d L : ℕ} {θ η : Point d} {S : ℝ}
    (hS : 0 ≤ S) (hθ : ‖θ‖ ≤ S) (hη : ‖η‖ ≤ S) :
    |pointInnerExpRemainder L θ η| ≤
      Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial := by
  have hinner : |inner ℝ θ η| ≤ S ^ 2 := by
    calc
      |inner ℝ θ η| ≤ ‖θ‖ * ‖η‖ := abs_real_inner_le_norm θ η
      _ ≤ S * S := mul_le_mul hθ hη (norm_nonneg η) hS
      _ = S ^ 2 := by ring
  simpa only [pointInnerExpRemainder, pointTruncatedInnerExp] using
    real_exp_taylor_remainder_bound L (sq_nonneg S) hinner











































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







theorem continuous_pointInnerExpRemainder (d L : ℕ) :
    Continuous fun z : Point d × Point d ↦
      pointInnerExpRemainder L z.1 z.2 := by
  unfold pointInnerExpRemainder pointTruncatedInnerExp
  fun_prop

theorem pointInnerExpRemainder_comp_integrable
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (y : Point d) (hyS : ‖y‖ ≤ S) :
    Integrable (fun a ↦ pointInnerExpRemainder L (θ a) y) μ := by
  let R := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial
  apply Integrable.of_bound
    ((continuous_pointInnerExpRemainder d L).measurable.comp
      (hθmeas.prodMk measurable_const) |>.aestronglyMeasurable) R
  exact Filter.Eventually.of_forall fun a ↦ by
    rw [Real.norm_eq_abs]
    exact abs_pointInnerExpRemainder_le hS (hθS a) hyS



theorem pointInnerExpRemainder_comp_comp_integrable
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    Integrable (fun z : Θ × Θ ↦
      pointInnerExpRemainder L (θ z.1) (θ z.2)) (μ.prod μ) := by
  let R := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial
  apply Integrable.of_bound
    ((continuous_pointInnerExpRemainder d L).measurable.comp
      ((hθmeas.comp measurable_fst).prodMk (hθmeas.comp measurable_snd))
      |>.aestronglyMeasurable) R
  exact Filter.Eventually.of_forall fun z ↦ by
    rw [Real.norm_eq_abs]
    exact abs_pointInnerExpRemainder_le hS (hθS z.1) (hθS z.2)





theorem exp_inner_eq_remainder_add_truncated {d : ℕ} (L : ℕ)
    (x y : Point d) :
    Real.exp (inner ℝ x y) =
      pointInnerExpRemainder L x y + pointTruncatedInnerExp L x y := by
  unfold pointInnerExpRemainder
  ring









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
theorem solution
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    (∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) +
        ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j)) =
      (∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j) := by
  let Aexp := ∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ
  let Arem := ∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ
  let Atrunc := ∫ a, ∫ b, pointTruncatedInnerExp L (θ b) (θ a) ∂μ ∂μ
  let Bexp := ∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ
  let Brem := ∑ i, w i * ∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ
  let Btrunc := ∑ i, w i * ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ
  let Cexp := ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j))
  let Crem := ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j)
  let Ctrunc := ∑ i, ∑ j, w i * w j * pointTruncatedInnerExp L (z i) (z j)
  have hExpDouble0 := exp_inner_comp_comp_integrable μ θ hθmeas hS hθS
  have hExpDouble : Integrable (fun q : Θ × Θ ↦
      Real.exp (inner ℝ (θ q.2) (θ q.1))) (μ.prod μ) := hExpDouble0.swap
  have hRemDouble0 := pointInnerExpRemainder_comp_comp_integrable
    (L := L) μ θ hθmeas hS hθS
  have hRemDouble : Integrable (fun q : Θ × Θ ↦
      pointInnerExpRemainder L (θ q.2) (θ q.1)) (μ.prod μ) := hRemDouble0.swap
  have hTruncDouble : Integrable (fun q : Θ × Θ ↦
      pointTruncatedInnerExp L (θ q.2) (θ q.1)) (μ.prod μ) := by
    apply (hExpDouble.sub hRemDouble).congr
    exact Filter.Eventually.of_forall fun q ↦ by
      change Real.exp (inner ℝ (θ q.2) (θ q.1)) -
          pointInnerExpRemainder L (θ q.2) (θ q.1) =
        pointTruncatedInnerExp L (θ q.2) (θ q.1)
      unfold pointInnerExpRemainder
      ring
  have hAeq : Aexp = Arem + Atrunc := by
    dsimp only [Aexp, Arem, Atrunc]
    rw [integral_integral hExpDouble, integral_integral hRemDouble,
      integral_integral hTruncDouble, ← integral_add hRemDouble hTruncDouble]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q ↦
      exp_inner_eq_remainder_add_truncated L (θ q.2) (θ q.1)
  have hsingle (i : ι) :
      (∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) =
        (∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ) +
          ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
    have he := exp_inner_comp_integrable μ θ hθmeas hS hθS (z i) (hzS i)
    have hr := pointInnerExpRemainder_comp_integrable
      (L := L) μ θ hθmeas hS hθS (z i) (hzS i)
    have ht := pointTruncatedInnerExp_comp_integrable μ θ hint (z i)
    rw [← integral_add hr ht]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a ↦
      exp_inner_eq_remainder_add_truncated L (θ a) (z i)
  have hBeq : Bexp = Brem + Btrunc := by
    dsimp only [Bexp, Brem, Btrunc]
    calc
      (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) =
          ∑ i, w i * ((∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ) +
            ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hsingle i]
      _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib]
  have hCeq : Cexp = Crem + Ctrunc := by
    dsimp only [Cexp, Crem, Ctrunc]
    calc
      (∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j))) =
          ∑ i, ∑ j, w i * w j *
            (pointInnerExpRemainder L (z i) (z j) +
              pointTruncatedInnerExp L (z i) (z j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [exp_inner_eq_remainder_add_truncated]
      _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib]
  have hzero : Atrunc - 2 * Btrunc + Ctrunc = 0 := by
    simpa only [Atrunc, Btrunc, Ctrunc] using
      moment_matching_truncated_quadratic_zero μ θ w z hint hmom
  change Aexp - 2 * Bexp + Cexp = Arem - 2 * Brem + Crem
  rw [hAeq, hBeq, hCeq]
  linarith

-- Prove2me | solution 1 for ReweightedNPMLE.abs_general_finite_remainder_quadratic_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:53:14.293829+00:00
-- url     : https://prove2.me/submissions/e2fcdcd5-398d-4856-bc03-c5e44387e220

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
import Theorems.Thm_ReweightedNPMLE_real_exp_taylor_remainder_bound

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

















theorem continuous_pointInnerExpRemainder (d L : ℕ) :
    Continuous fun z : Point d × Point d ↦
      pointInnerExpRemainder L z.1 z.2 := by
  unfold pointInnerExpRemainder pointTruncatedInnerExp
  fun_prop



theorem abs_integral_pointInnerExpRemainder_comp_le
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (y : Point d) (hyS : ‖y‖ ≤ S) :
    |∫ a, pointInnerExpRemainder L (θ a) y ∂μ| ≤
      Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial := by
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := μ)
    (C := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial)
    (f := fun a ↦ pointInnerExpRemainder L (θ a) y)
    (Filter.Eventually.of_forall fun a ↦ by
      rw [Real.norm_eq_abs]
      exact abs_pointInnerExpRemainder_le hS (hθS a) hyS)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hnorm

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

theorem abs_integral_integral_pointInnerExpRemainder_le
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    |∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ| ≤
      Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial := by
  have hrem := pointInnerExpRemainder_comp_comp_integrable
    (L := L) μ θ hθmeas hS hθS
  have hrem' : Integrable (fun z : Θ × Θ ↦
      pointInnerExpRemainder L (θ z.2) (θ z.1)) (μ.prod μ) := hrem.swap
  rw [integral_integral hrem']
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := μ.prod μ)
    (C := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial)
    (f := fun z : Θ × Θ ↦ pointInnerExpRemainder L (θ z.2) (θ z.1))
    (Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs]
      exact abs_pointInnerExpRemainder_le hS (hθS z.2) (hθS z.1))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hnorm













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
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    |(∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j)| ≤
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial) := by
  let R := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial
  let A := ∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ
  let B := ∑ i, w i * ∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ
  let C := ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j)
  have hA : |A| ≤ R := by
    simpa only [A, R] using
      abs_integral_integral_pointInnerExpRemainder_le
        (L := L) μ θ hθmeas hS hθS
  have hBi (i : ι) :
      |∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ| ≤ R := by
    simpa only [R] using
      (abs_integral_pointInnerExpRemainder_comp_le
        (d := d) (L := L) (Θ := Θ) μ θ hS hθS (z i) (hzS i))
  have hsumR : (∑ i, w i * R) = R := by
    calc
      (∑ i, w i * R) = (∑ i, w i) * R := by
        simpa using (Finset.sum_mul Finset.univ w R).symm
      _ = R := by rw [hwsum, one_mul]
  have hB : |B| ≤ R := by
    calc
      |B| ≤ ∑ i, |w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, w i * |∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_nonneg (hw i)]
      _ ≤ ∑ i, w i * R := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hBi i) (hw i)
      _ = R := hsumR
  have hC : |C| ≤ R := by
    calc
      |C| ≤ ∑ i, |∑ j,
          w i * w j * pointInnerExpRemainder L (z i) (z j)| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j,
          |w i * w j * pointInnerExpRemainder L (z i) (z j)| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, ∑ j,
          w i * w j * |pointInnerExpRemainder L (z i) (z j)| := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (hw i), abs_of_nonneg (hw j)]
      _ ≤ ∑ i, ∑ j, w i * w j * R := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (abs_pointInnerExpRemainder_le hS (hzS i) (hzS j))
          (mul_nonneg (hw i) (hw j))
      _ = R := by
        calc
          (∑ i, ∑ j, w i * w j * R) =
              ∑ i, w i * (∑ j, w j) * R := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum, Finset.sum_mul]
          _ = ∑ i, w i * R := by rw [hwsum]; simp
          _ = R := hsumR
  change |A - 2 * B + C| ≤ 4 * R
  calc
    |A - 2 * B + C| ≤ |A - 2 * B| + |C| := abs_add_le _ _
    _ ≤ (|A| + |2 * B|) + |C| :=
      add_le_add (abs_sub A (2 * B)) (le_refl |C|)
    _ = (|A| + 2 * |B|) + |C| := by rw [abs_mul]; norm_num
    _ ≤ (R + 2 * R) + R := by nlinarith
    _ = 4 * R := by ring

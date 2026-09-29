-- Prove2me | solution 1 for BanditAlgorithm.standardGaussian_mills_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T23:32:00.388816+00:00
-- url     : https://prove2.me/submissions/9fcb8975-3b29-4062-b03e-9df7df7035d2

import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem standardGaussian_real_Ioi_eq_integral_mills (u : ℝ) :
    (gaussianReal 0 1).real (Set.Ioi u) =
      ∫ x in Set.Ioi u, gaussianPDFReal 0 1 x := by
  rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num) (Set.Ioi u)]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg (fun x ↦ gaussianPDFReal_nonneg 0 1 x)

end BanditAlgorithm

open BanditAlgorithm

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ u : ℝ, 0 ≤ u →
        c / (u + 1) * Real.exp (-u ^ 2 / 2) ≤
          (gaussianReal 0 1).real (Set.Ioi u) := by
  let c : ℝ := Real.exp (-(3 : ℝ) / 2) /
    Real.sqrt (2 * Real.pi)
  refine ⟨c, by
    dsimp [c]
    positivity, ?_⟩
  intro u hu
  have hu1 : 0 < u + 1 := by linarith
  let d : ℝ := 1 / (u + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdle : d ≤ 1 := by
    dsimp [d]
    exact (div_le_one hu1).2 (by linarith)
  have hdrel : d * (u + 1) = 1 := by
    dsimp [d]
    field_simp
  have hsq (x : ℝ) (hx : x ∈ Set.Ioc u (u + d)) :
      x ^ 2 ≤ u ^ 2 + 3 := by
    have hxu : u < x := hx.1
    have hxud : x ≤ u + d := hx.2
    have hx0 : 0 ≤ x := hu.trans hxu.le
    have hsqmono : x ^ 2 ≤ (u + d) ^ 2 := by nlinarith
    have hudprod : u * d ≤ 1 := by
      have : u * d ≤ (u + 1) * d := by nlinarith
      nlinarith [hdrel]
    have hd2 : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
    nlinarith
  have hpdf (x : ℝ) (hx : x ∈ Set.Ioc u (u + d)) :
      c * Real.exp (-u ^ 2 / 2) ≤ gaussianPDFReal 0 1 x := by
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, zero_add, sub_zero]
    have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    have hexp :
        Real.exp (-(3 : ℝ) / 2) * Real.exp (-u ^ 2 / 2) ≤
          Real.exp (-(x ^ 2) / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hsq x hx]
    dsimp [c]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith [inv_pos.mpr (show 0 < Real.sqrt (2 * Real.pi) by positivity)]
  rw [standardGaussian_real_Ioi_eq_integral_mills]
  calc
    c / (u + 1) * Real.exp (-u ^ 2 / 2) =
        d * (c * Real.exp (-u ^ 2 / 2)) := by
          dsimp [d]
          ring
    _ = ∫ _x in Set.Ioc u (u + d),
          c * Real.exp (-u ^ 2 / 2) ∂volume := by
          simp [hd.le]
    _ ≤ ∫ x in Set.Ioc u (u + d), gaussianPDFReal 0 1 x ∂volume := by
          apply setIntegral_mono_on
          · exact integrableOn_const (by simp)
          · exact (integrable_gaussianPDFReal 0 1).integrableOn
          · exact measurableSet_Ioc
          · intro x hx
            exact hpdf x hx
    _ ≤ ∫ x in Set.Ioi u, gaussianPDFReal 0 1 x ∂volume := by
          apply setIntegral_mono_set
          · exact (integrable_gaussianPDFReal 0 1).integrableOn
          · exact ae_of_all _ (gaussianPDFReal_nonneg 0 1)
          · exact ae_of_all _ Set.Ioc_subset_Ioi_self

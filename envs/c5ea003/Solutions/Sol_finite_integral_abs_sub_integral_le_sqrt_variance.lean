-- Prove2me | solution 1 for finite_integral_abs_sub_integral_le_sqrt_variance
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-07-04T01:53:28.941028+00:00
-- url     : https://prove2.me/submissions/484a09c3-5a7b-4df8-be8f-01b15fad75de

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

open MeasureTheory

/-
Paper source: "Buying to Bundle: Optimal Sourcing from Monopolistic Sellers",
Appendix C.2, proof of Theorem 4.6, p. 35, Eq. (5).

This is the formal Jensen/Cauchy-Schwarz bridge used in Eq. (5): on a finite
probability space, the first absolute centered moment is bounded by the square
root of the variance.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] [Finite Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) :
    ∫ ω, |Y ω - ∫ x, Y x ∂μ| ∂μ ≤ Real.sqrt (ProbabilityTheory.variance Y μ) := by
  let Z : Ω → ℝ := fun ω => Y ω - ∫ x, Y x ∂μ
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := memLp_const 1
  have hg : MemLp (fun ω => |Z ω|) (ENNReal.ofReal (2 : ℝ)) μ := by
    exact ⟨AEStronglyMeasurable.of_discrete, eLpNorm_lt_top_of_finite⟩
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hholder
      (f := fun _ : Ω => (1 : ℝ)) (g := fun ω => |Z ω|)
      (by filter_upwards with ω; norm_num)
      (by filter_upwards with ω; exact abs_nonneg (Z ω))
      hone hg
  have hcs' : ∫ a, |Z a| ∂μ ≤ (∫ a, |Z a| ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by
    simpa [one_mul] using hcs
  have hvar : ProbabilityTheory.variance Y μ = ∫ ω, Z ω ^ 2 ∂μ := by
    rw [ProbabilityTheory.variance_eq_integral
      (hX := (AEStronglyMeasurable.of_discrete (f := Y)).aemeasurable)]
  have hint_abs_sq : (∫ a, |Z a| ^ (2 : ℝ) ∂μ) = ∫ a, Z a ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    rw [Real.rpow_two, sq_abs]
  rw [hint_abs_sq] at hcs'
  have hroot2 : (∫ a, Z a ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ =
      Real.sqrt (ProbabilityTheory.variance Y μ) := by
    rw [← hvar, Real.sqrt_eq_rpow]
    norm_num
  exact hcs'.trans_eq hroot2

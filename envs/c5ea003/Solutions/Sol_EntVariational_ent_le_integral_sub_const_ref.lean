-- Prove2me | solution 1 for EntVariational.ent_le_integral_sub_const_ref
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T04:19:24.746994+00:00
-- url     : https://prove2.me/submissions/89f7480f-924b-407b-b2da-0c1eb6f476da

import Theorems.Thm_ScalarGibbs_mul_log_sub_mul_log_sub_sub_nonneg
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Real MeasureTheory

theorem solution
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {Y : α → ℝ} {u : ℝ}
    (hY_nonneg : ∀ x, 0 ≤ Y x)
    (hY_int : Integrable Y μ)
    (hYlog_int : Integrable (fun x ↦ Y x * Real.log (Y x)) μ)
    (hu : 0 < u) :
    (∫ x, Y x * Real.log (Y x) ∂μ) - (∫ x, Y x ∂μ) * Real.log (∫ x, Y x ∂μ)
      ≤ ∫ x, (Y x * Real.log (Y x) - Y x * Real.log u - (Y x - u)) ∂μ := by
  set m : ℝ := ∫ x, Y x ∂μ with hm
  have hm_nonneg : 0 ≤ m := by rw [hm]; exact integral_nonneg hY_nonneg
  have hconst_int : Integrable (fun _ : α ↦ u) μ := integrable_const u
  have hYlogu_int : Integrable (fun x ↦ Y x * Real.log u) μ := hY_int.mul_const _
  have hsplit : (∫ x, (Y x * Real.log (Y x) - Y x * Real.log u - (Y x - u)) ∂μ)
      = (∫ x, Y x * Real.log (Y x) ∂μ) - (Real.log u) * m - (m - u) := by
    have hfirst_int : Integrable (fun x ↦ Y x * Real.log (Y x) - Y x * Real.log u) μ :=
      hYlog_int.sub hYlogu_int
    have hsecond_int : Integrable (fun x ↦ Y x - u) μ := hY_int.sub hconst_int
    have e1 : (∫ x, (Y x * Real.log (Y x) - Y x * Real.log u - (Y x - u)) ∂μ)
        = (∫ x, (Y x * Real.log (Y x) - Y x * Real.log u) ∂μ) - (∫ x, (Y x - u) ∂μ) := by
      rw [← integral_sub hfirst_int hsecond_int]
    rw [e1]
    rw [integral_sub hYlog_int hYlogu_int, integral_sub hY_int hconst_int]
    have hconst_eval : (∫ _x : α, u ∂μ) = u := by simp
    rw [integral_mul_const, hconst_eval, ← hm]
    ring
  rw [hsplit]
  have hgibbs : 0 ≤ m * Real.log m - m * Real.log u - (m - u) :=
    ScalarGibbs.mul_log_sub_mul_log_sub_sub_nonneg hm_nonneg hu
  nlinarith [hgibbs]

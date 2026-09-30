-- Prove2me | solution 1 for RybinAI2026.P01.psi_rational_derivative_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T00:19:31.774983+00:00
-- url     : https://prove2.me/submissions/42370a75-7993-48bd-bcb1-8a098c402466

import Mathlib

open MeasureTheory

theorem solution (t : ℝ) (ht : 0 < t) :
    ∫ s in (0 : ℝ)..1, (1 - (t - 1) * s ^ 2) / (1 + (t - 1) * s ^ 2) ^ 2 = 1 / t := by
  let f : ℝ → ℝ := fun s => s / (1 + (t - 1) * s ^ 2)
  let f' : ℝ → ℝ := fun s => (1 - (t - 1) * s ^ 2) / (1 + (t - 1) * s ^ 2) ^ 2
  have hden : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + (t - 1) * s ^ 2 := by
    intro s hs
    by_cases h : t ≤ 1
    · have hs2 : s ^ 2 ≤ 1 := by
        have hmul := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hs2 (sub_nonneg.mpr h)
      nlinarith
    · have ht1 : 1 < t := lt_of_not_ge h
      nlinarith [sq_nonneg s]
  have hden_cont : ContinuousOn
      (fun s : ℝ => 1 + (t - 1) * s ^ 2) (Set.uIcc 0 1) := by fun_prop
  have hden_ne : ∀ s ∈ Set.uIcc (0 : ℝ) 1, 1 + (t - 1) * s ^ 2 ≠ 0 := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using hs
    exact ne_of_gt (hden s hs')
  have hf_cont : ContinuousOn f (Set.uIcc 0 1) := by
    apply continuousOn_id.div hden_cont
    exact hden_ne
  have hf'_cont : ContinuousOn f' (Set.uIcc 0 1) := by
    have hnum : ContinuousOn (fun s : ℝ => 1 - (t - 1) * s ^ 2) (Set.uIcc 0 1) := by fun_prop
    have hden2 : ContinuousOn (fun s : ℝ => (1 + (t - 1) * s ^ 2) ^ 2)
        (Set.uIcc 0 1) := hden_cont.pow 2
    apply hnum.div hden2
    intro s hs
    exact pow_ne_zero _ (hden_ne s hs)
  have hf'_int : IntervalIntegrable f' volume 0 1 := hf'_cont.intervalIntegrable
  have hderiv (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt f (f' s) s := by
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
    have hd : 0 < 1 + (t - 1) * s ^ 2 := hden s hs'
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
      convert (hasDerivAt_id' s).pow 2 using 1 <;> ring
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 s := hasDerivAt_const s 1
    have hq := hsq.const_mul (t - 1)
    have hden' : HasDerivAt (fun x : ℝ => 1 + (t - 1) * x ^ 2)
        (2 * (t - 1) * s) s := by
      convert hconst.add hq using 1 <;> ring
    have hquot := (hasDerivAt_id' s).div hden' (ne_of_gt hd)
    convert hquot using 1 <;> dsimp [f, f'] <;> field_simp [ne_of_gt hd] <;> ring
  have hf_cont' : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le zero_le_one] using hf_cont
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    zero_le_one hf_cont' (fun s hs => hderiv s hs) hf'_int
  have hvalue : f 1 - f 0 = 1 / t := by
    dsimp [f]
    field_simp [ne_of_gt ht]
    ring
  simpa [f', hvalue] using hftc

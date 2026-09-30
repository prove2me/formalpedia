-- Prove2me | solution 1 for lean_workbook_plus_35072
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:16.335742+00:00
-- url     : https://prove2.me/submissions/5b612676-bbbd-4b53-bc13-f1155e226843

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f (f x) = 1 - x^2) : f 1 = 0 ∧ f 0 = 1 := by
  exfalso
  have h1 : f (f 0) = 1 := by
    have := hf 0
    norm_num at this
    exact this
  have h2 : f (f 1) = 0 := by
    have := hf 1
    norm_num at this
    exact this
  have h3 : f 1 = 1 - (f 0) ^ 2 := by
    have := hf (f 0)
    rw [h1] at this
    exact this
  have h4 : f 0 = 1 - (f 1) ^ 2 := by
    have := hf (f 1)
    rw [h2] at this
    exact this
  have key : (f 1 - f 0) * (f 1 + f 0 - 1) = 0 := by
    linear_combination h4 - h3
  rcases mul_eq_zero.mp key with h | h
  · have e : f 1 = f 0 := by linarith
    rw [e, h1] at h2
    norm_num at h2
  · have hy : f 0 * (f 0 - 1) = 0 := by
      linear_combination h3 - h
    rcases mul_eq_zero.mp hy with h0 | h0
    · rw [h0] at h1
      rw [h0] at h1
      norm_num at h1
    · have h0' : f 0 = 1 := by linarith
      have hv : f 1 = 0 := by linarith
      rw [hv, h0'] at h2
      norm_num at h2

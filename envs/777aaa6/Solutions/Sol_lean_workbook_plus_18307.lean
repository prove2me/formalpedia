-- Prove2me | solution 1 for lean_workbook_plus_18307
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:42:25.365491+00:00
-- url     : https://prove2.me/submissions/6dea6e20-321c-4a9b-87fc-b5898d2d38c6

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c k : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a * b + b * c + c * a = 1 ∧ k > 0 → (a * b + k) / (a + b) + (b * c + k) / (b + c) + (c * a + k) / (c + a) ≤ (k - 7) / 2) := by
  intro h
  have h1 := h 1 1 0 1 ⟨by norm_num, by norm_num, le_refl 0, by norm_num, by norm_num⟩
  have e1 : ((1:ℝ) * 1 + 1) / (1 + 1) = 1 := by norm_num
  have e2 : ((1:ℝ) * 0 + 1) / (1 + 0) = 1 := by norm_num
  have e3 : ((0:ℝ) * 1 + 1) / (0 + 1) = 1 := by norm_num
  have e4 : ((1:ℝ) - 7) / 2 = -3 := by norm_num
  rw [e1, e2, e3, e4] at h1
  norm_num at h1

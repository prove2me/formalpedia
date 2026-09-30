-- Prove2me | solution 1 for lean_workbook_plus_16360
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:46.359536+00:00
-- url     : https://prove2.me/submissions/39f5375e-12b3-4eb6-9ea9-0e5616ad49eb

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h₁ : a ≤ b + c) (h₂ : a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1) :
  (1 - a) * (1 - b) * (1 - c) ≥ 0 := by
  obtain ⟨ha, hb, hc⟩ := h₂
  apply mul_nonneg (mul_nonneg _ _) _ <;> linarith

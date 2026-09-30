-- Prove2me | solution 1 for lean_workbook_plus_2
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:11.66137+00:00
-- url     : https://prove2.me/submissions/697f5d72-5fd5-4e40-8453-1861a99120a3

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : x^2 - 2*x - 24 < 0 ↔ x ∈ Set.Ioo (-4) 6 := by
  rw [Set.mem_Ioo]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x - 1)]
  · rintro ⟨h1, h2⟩
    nlinarith [mul_pos (by linarith : (0:ℝ) < x + 4) (by linarith : (0:ℝ) < 6 - x)]

-- Prove2me | solution 1 for lean_workbook_plus_82301
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:06:56.056696+00:00
-- url     : https://prove2.me/submissions/1a2d5845-668d-4c2c-a91f-d987c3509032

import Mathlib

theorem solution : ¬ (∀ x : ℝ, 0 < x ∧ x < 1 →
    Real.sqrt (1 + x^2) > Real.sqrt (1 + x)) := by
  intro h
  have hle : Real.sqrt (1 + (1 / 2 : ℝ)^2) ≤ Real.sqrt (1 + (1 / 2 : ℝ)) :=
    Real.sqrt_le_sqrt (by norm_num)
  exact (not_lt_of_ge hle) (h (1 / 2) (by norm_num))

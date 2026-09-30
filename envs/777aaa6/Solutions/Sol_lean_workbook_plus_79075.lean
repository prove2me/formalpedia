-- Prove2me | solution 1 for lean_workbook_plus_79075
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:17.203892+00:00
-- url     : https://prove2.me/submissions/4de72329-5535-40ba-a259-9d230cbaaea9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ a b c : ℝ,
    (1 - a ^ 2) / (1 + a ^ 2) + (1 - b ^ 2) / (1 + b ^ 2) +
      (1 - c ^ 2) / (1 + c ^ 2) ≥ 0) := by
  intro h
  have hh := h 2 2 2
  have he : (1 - (2 : ℝ)^2) / (1 + 2^2) + (1 - 2^2) / (1 + 2^2) +
      (1 - 2^2) / (1 + 2^2) = -9 / 5 := by ring
  rw [he] at hh
  norm_num at hh

#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_58439
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:11:50.708788+00:00
-- url     : https://prove2.me/submissions/8d65923f-ec1f-444d-8f8c-50971e3b3a22

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, (1 / (a ^ 2 + b ^ 2 + 3) + 1 / (b ^ 2 + c ^ 2 + 3) + 1 / (c ^ 2 + a ^ 2 + 3)) ≤ 3 / 5) := by
  intro h
  have := h 0 0 0
  norm_num at this
